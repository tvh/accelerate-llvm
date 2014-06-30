{-# LANGUAGE CPP                      #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeOperators            #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute (

  executeAcc, executeAfun1,

  executeOp,

) where

-- accelerate
import Data.Array.Accelerate                                    ( arrayShape )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Execute

import Data.Array.Accelerate.LLVM.Native.Array.Data
import Data.Array.Accelerate.LLVM.Native.Compile
import Data.Array.Accelerate.LLVM.Native.Execute.Async
import Data.Array.Accelerate.LLVM.Native.Execute.Environment
import Data.Array.Accelerate.LLVM.Native.Execute.Marshal
import Data.Array.Accelerate.LLVM.Native.Target

-- Use work-stealing scheduler
import Data.Range.Range                                         ( Range(..) )
import Control.Parallel.Meta                                    ( runExecutable, Finalise )
import Control.Parallel.Meta.Worker                             ( gangSize )
import Data.Array.Accelerate.LLVM.Native.Execute.LBS

-- library
import Prelude                                                  hiding ( map, scanl, scanr, last )
import Data.Monoid                                              ( mempty )
import Data.Word                                                ( Word8 )
import Control.Monad.State                                      ( gets )
import Control.Monad.Trans                                      ( liftIO )
import qualified Prelude                                        as P

import Foreign.LibFFI                                           as FFI
import Foreign.C
import Foreign.Ptr

#if !MIN_VERSION_llvm_general(3,3,0)
import Data.Word
import Data.Maybe
import qualified LLVM.General.Context                           as LLVM
#endif

-- Array expression evaluation
-- ---------------------------

-- Computations are evaluated by traversing the AST bottom up, and for each node
-- distinguishing between three cases:
--
--  1. If it is a Use node, we return a reference to the array data. Even though
--     we execute with multiple cores, we assume a shared memory multiprocessor
--     machine.
--
--  2. If it is a non-skeleton node, such as a let binding or shape conversion,
--     then execute directly by updating the environment or similar.
--
--  3. If it is a skeleton node, then we need to execute the generated LLVM
--     code.
--
instance Execute Native where
  map           = simpleOp
  generate      = simpleOp
  transform     = simpleOp
  backpermute   = simpleOp
  fold          = foldOp
  fold1         = fold1Op
  permute       = permuteOp
  scanl         = scanlOp
  scanl1        = scanl1Op
  scanl'        = scanl'Op
  scanr         = scanrOp
  scanr1        = scanr1Op
  scanr'        = scanr'Op
  foldSeg       = foldSegOp
  fold1Seg      = foldSegOp
  stencil1      = stencil1Op
  stencil2      = stencil2Op


-- Skeleton implementation
-- -----------------------

-- Execute fold operations. There are two flavours:
--
--   1. If we are collapsing to a single value, then the threads compute an
--   individual partial sum, then a single thread adds the results.
--
--   2. If this is a multidimensional reduction, then threads reduce the
--   inner dimensions sequentially.
--
fold1Op
    :: (Shape sh, Elt e)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> (sh :. Int)
    -> LLVM Native (Array sh e)
fold1Op kernel gamma aenv stream sh@(_ :. sz)
  = $boundsCheck "fold1" "empty array" (sz > 0)
  $ foldCore kernel gamma aenv stream sh False

-- Make space for the neutral element
foldOp
    :: (Shape sh, Elt e)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> (sh :. Int)
    -> LLVM Native (Array sh e)
foldOp kernel gamma aenv stream (sh :. sz)
  = let sh' = listToShape . P.map (max 1) . shapeToList $ sh
        shEmpty = shapeToList sh /= shapeToList sh'
    in foldCore kernel gamma aenv stream (sh' :. sz) shEmpty

foldCore
    :: forall aenv sh e. (Shape sh, Elt e)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> (sh :. Int)
    -> Bool
    -> LLVM Native (Array sh e)
foldCore (NativeR k) gamma aenv () (sh :. sz) shEmpty = do
  native@Native{..} <- gets llvmTarget

  -- Either (1) multidimensional reduction; or
  --        (2) sequential reduction
  if dim sh > 0 || gangSize theGang == 1
     then do let out = allocateArray sh
                 ppt = defaultSmallPPT `max` (defaultLargePPT `div` sz)
             --
             liftIO $ do
               executeFunction k                                 $ \f ->
                 runExecutable fillP ppt (IE 0 (size sh)) mempty $ \start end _ ->
                   callFFI f retVoid =<< marshal native () (start, end, shEmpty, sz, out, (gamma,aenv))

             return out

  -- Parallel reduction
     else do let chunks = gangSize theGang
                 tmp    = allocateArray (sh :. chunks)  :: Array (sh:.Int) e
                 out    = allocateArray sh
                 n      = sz `min` chunks
             --
             liftIO $ do
               executeNamedFunction k "fold1"                                     $ \f ->
                 runExecutable fillP defaultLargePPT (IE 0 (size sh * sz)) mempty $ \start end tid ->
                   callFFI f retVoid =<< marshal native () (start,end,tid,tmp,(gamma,aenv))

               executeNamedFunction k "foldAll" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int,n,tmp,out,(gamma,aenv))

             return out

foldSegOp
    :: forall aenv sh e. (Shape sh, Elt e)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> (sh :. Int)
    -> DIM1
    -> LLVM Native (Array (sh:.Int) e)
foldSegOp (NativeR k) gamma aenv () (sh :. n) (Z  :. sz) = do
  native@Native{..} <- gets llvmTarget

  let out = allocateArray (sh :. (sz-1))
      ppt = defaultSmallPPT `max` (defaultLargePPT `div` sz)

  liftIO $ do
    executeFunction k                                 $ \f ->
      runExecutable fillP ppt (IE 0 (size sh * (sz-1))) mempty $ \start end _ ->
        callFFI f retVoid =<< marshal native () (start, end, n, out, (gamma,aenv))

  return out


-- Forward permutation, specified by an indexing mapping into an array and a
-- combination function to combine elements.
--
permuteOp
    :: (Shape sh, Shape sh', Elt e)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> sh
    -> Array sh' e
    -> LLVM Native (Array sh' e)
permuteOp kernel gamma aenv () shIn dfs = do
  let
      barrier :: Vector Word8
      barrier@(Array _ adata)   = allocateArray (Z :. n)
      ((), ptr)                 = ptrsOfArrayData adata
      n                         = size (shape dfs)
      unlocked                  = 0
  --
  out    <- cloneArray dfs
  native <- gets llvmTarget
  liftIO $ do
    memset ptr unlocked n
    executeOp native kernel mempty gamma aenv (IE 0 (size shIn)) (barrier, out)
  return out

-- Left inclusive scan
--
scanlOp
    :: forall aenv e. Elt e
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> DIM1
    -> LLVM Native (Vector e)
scanlOp (NativeR k) gamma aenv () (Z :. sz) = do
  native@Native{..} <- gets llvmTarget

  -- sequential reduction
  if gangSize theGang == 1 || sz < defaultLargePPT
     then do let tmp = allocateArray (Z :. 0) :: Vector e
                 out = allocateArray (Z :. sz+1)
             --
             liftIO $ do
               executeNamedFunction k "scanl" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int, 1::Int, 0::Int, sz, sz, tmp, out, (gamma,aenv))

             return out

  -- Parallel reduction
     else do let chunkSize = defaultLargePPT
                 chunks    = sz `div` chunkSize
                 tmp       = allocateArray (Z :. (chunks-1)) :: Vector e
                 out       = allocateArray (Z :. sz+1)
             --
             liftIO $ do
               executeNamedFunction k "scanl1Pre"           $ \f -> do
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,chunkSize,tmp,(gamma,aenv))

               executeNamedFunction k "scanl"          $ \f ->
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,(chunks-1),chunkSize,sz,tmp,out,(gamma,aenv))

             return out

-- Left inclusive scan
--
scanl1Op
    :: forall aenv e. Elt e
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> DIM1
    -> LLVM Native (Vector e)
scanl1Op (NativeR k) gamma aenv () (Z :. sz) = do
  native@Native{..} <- gets llvmTarget

  -- sequential reduction
  if gangSize theGang == 1 || sz < defaultLargePPT
     then do let tmp = allocateArray (Z :. 0) :: Vector e
                 out = allocateArray (Z :. sz)
             --
             liftIO $ do
               executeNamedFunction k "scanl1" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int, 1::Int, 0::Int, sz, sz, tmp, out, (gamma,aenv))

             return out

  -- Parallel reduction
     else do let chunkSize = defaultLargePPT
                 chunks    = sz `div` chunkSize
                 tmp       = allocateArray (Z :. (chunks-1)) :: Vector e
                 out       = allocateArray (Z :. sz)
             --
             liftIO $ do
               executeNamedFunction k "scanl1Pre"           $ \f -> do
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,chunkSize,tmp,(gamma,aenv))

               executeNamedFunction k "scanl1"          $ \f ->
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,(chunks-1),chunkSize,sz,tmp,out,(gamma,aenv))

             return out

-- Left inclusive scan
--
scanl'Op
    :: forall aenv e. Elt e
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> DIM1
    -> LLVM Native (Vector e, Scalar e)
scanl'Op (NativeR k) gamma aenv () (Z :. sz) = do
  native@Native{..} <- gets llvmTarget

  -- sequential reduction
  if gangSize theGang == 1 || sz < defaultLargePPT
     then do let tmp  = allocateArray (Z :. 0) :: Vector e
                 out  = allocateArray (Z :. sz)
                 last = allocateArray Z
             --
             liftIO $ do
               executeNamedFunction k "scanl" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int,1::Int,0::Int,sz,sz,tmp,out,last,(gamma,aenv))

             return (out, last)

  -- Parallel reduction
     else do let chunkSize = defaultLargePPT
                 chunks    = sz `div` chunkSize
                 tmp       = allocateArray (Z :. (chunks-1)) :: Vector e
                 out       = allocateArray (Z :. sz)
                 last      = allocateArray Z
             --
             liftIO $ do
               executeNamedFunction k "scanl1Pre"           $ \f -> do
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,chunkSize,tmp,(gamma,aenv))

               executeNamedFunction k "scanl"               $ \f ->
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,(chunks-1),chunkSize,sz,tmp,out,last,(gamma,aenv))

             return (out, last)

-- Right inclusive scan
--
scanrOp
    :: forall aenv e. Elt e
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> DIM1
    -> LLVM Native (Vector e)
scanrOp (NativeR k) gamma aenv () (Z :. sz) = do
  native@Native{..} <- gets llvmTarget

  -- sequential reduction
  if gangSize theGang == 1 || sz < defaultLargePPT
     then do let tmp = allocateArray (Z :. 0) :: Vector e
                 out = allocateArray (Z :. sz+1)
             --
             liftIO $ do
               executeNamedFunction k "scanr" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int, 1::Int, 0::Int, sz, sz, tmp, out, (gamma,aenv))

             return out

  -- Parallel reduction
     else do let chunkSize = defaultLargePPT
                 chunks    = sz `div` chunkSize
                 tmp       = allocateArray (Z :. (chunks-1)) :: Vector e
                 out       = allocateArray (Z :. sz+1)
             --
             liftIO $ do
               executeNamedFunction k "scanr1Pre"           $ \f -> do
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,chunkSize,sz,tmp,(gamma,aenv))

               executeNamedFunction k "scanr"          $ \f ->
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,(chunks-1),chunkSize,sz,tmp,out,(gamma,aenv))

             return out

-- Right inclusive scan
--
scanr1Op
    :: forall aenv e. Elt e
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> DIM1
    -> LLVM Native (Vector e)
scanr1Op (NativeR k) gamma aenv () (Z :. sz) = do
  native@Native{..} <- gets llvmTarget

  -- sequential reduction
  if gangSize theGang == 1 || sz < defaultLargePPT
     then do let tmp = allocateArray (Z :. 0) :: Vector e
                 out = allocateArray (Z :. sz)
             --
             liftIO $ do
               executeNamedFunction k "scanr1" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int, 1::Int, 0::Int, sz, sz, tmp, out, (gamma,aenv))

             return out

  -- Parallel reduction
     else do let chunkSize = defaultLargePPT
                 chunks    = sz `div` chunkSize
                 tmp       = allocateArray (Z :. (chunks-1)) :: Vector e
                 out       = allocateArray (Z :. sz)
             --
             liftIO $ do
               executeNamedFunction k "scanr1Pre"           $ \f -> do
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,chunkSize,sz,tmp,(gamma,aenv))

               executeNamedFunction k "scanr1"          $ \f ->
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,(chunks-1),chunkSize,sz,tmp,out,(gamma,aenv))

             return out


-- Right inclusive scan
--
scanr'Op
    :: forall aenv e. Elt e
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> DIM1
    -> LLVM Native (Vector e, Scalar e)
scanr'Op (NativeR k) gamma aenv () (Z :. sz) = do
  native@Native{..} <- gets llvmTarget

  -- sequential reduction
  if gangSize theGang == 1 || sz < defaultLargePPT
     then do let tmp  = allocateArray (Z :. 0) :: Vector e
                 out  = allocateArray (Z :. sz)
                 last = allocateArray Z
             --
             liftIO $ do
               executeNamedFunction k "scanr" $ \f ->
                 callFFI f retVoid =<< marshal native () (0::Int,1::Int,0::Int,sz,sz,tmp,out,last,(gamma,aenv))

             return (out, last)

  -- Parallel reduction
     else do let chunkSize = defaultLargePPT
                 chunks    = sz `div` chunkSize
                 tmp       = allocateArray (Z :. (chunks-1)) :: Vector e
                 out       = allocateArray (Z :. sz)
                 last      = allocateArray Z
             --
             liftIO $ do
               executeNamedFunction k "scanr1Pre"           $ \f -> do
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,chunkSize,tmp,(gamma,aenv))

               executeNamedFunction k "scanr"               $ \f ->
                 runExecutable fillP 1 (IE 0 chunks) mempty $ \start end _ -> do
                   callFFI f retVoid =<< marshal native () (start,end,(chunks-1),chunkSize,sz,tmp,out,last,(gamma,aenv))

             return (out, last)

stencil1Op
    :: (Shape sh, Elt a, Elt b)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> Array sh a
    -> LLVM Native (Array sh b)
stencil1Op kernel gamma aenv () arr = do
  let sh = arrayShape arr
      out = allocateArray sh
  native <- gets llvmTarget
  liftIO  $ executeOp native kernel mempty gamma aenv (IE 0 (size sh)) (arr,out)
  return out

stencil2Op
    :: (Shape sh, Elt a, Elt b, Elt c)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> Array sh a
    -> Array sh b
    -> LLVM Native (Array sh c)
stencil2Op kernel gamma aenv () arr1 arr2 = do
  let sh = arrayShape arr1
      out = allocateArray sh
  native <- gets llvmTarget
  liftIO  $ executeOp native kernel mempty gamma aenv (IE 0 (size sh)) (arr1,arr2,out)
  return out


-- Skeleton execution
-- ------------------

-- Simple kernels just needs to know the shape of the output array.
--
simpleOp
    :: (Shape sh, Elt e)
    => ExecutableR Native
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> sh
    -> LLVM Native (Array sh e)
simpleOp kernel gamma aenv () sh = do
  let out = allocateArray sh
  native <- gets llvmTarget
  liftIO  $ executeOp native kernel mempty gamma aenv (IE 0 (size sh)) out
  return out


-- JIT compile the LLVM code representing this kernel, link to the running
-- executable, and execute the main function using the 'fillP' method to
-- distribute work evenly amongst the threads.
--
executeOp
    :: Marshalable args
    => Native
    -> ExecutableR Native
    -> Finalise
    -> Gamma aenv
    -> Aval aenv
    -> Range
    -> args
    -> IO ()
executeOp native@Native{..} (NativeR main) finish gamma aenv r args =
  executeFunction main                        $ \f ->
  runExecutable fillP defaultLargePPT r finish $ \start end _ ->
    callFFI f retVoid =<< marshal native () (start, end, args, (gamma,aenv))


-- Standard C functions
-- --------------------

memset :: Ptr Word8 -> Word8 -> Int -> IO ()
memset p w s = c_memset p (fromIntegral w) (fromIntegral s) >> return ()

foreign import ccall unsafe "string.h memset" c_memset
    :: Ptr Word8 -> CInt -> CSize -> IO (Ptr Word8)

