{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Fold
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Fold
  where

-- llvm-general
import LLVM.General.AST
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Analysis.Shape
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop

-- standard library
import GHC.Conc
import Prelude hiding (fromIntegral)


-- Reduce an array along the innermost dimension
--
mkFold
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold aenv f z a
  -- Either (1) multidimensional fold; or
  --        (2) only using one CPU, so just execute sequentially
  | numCapabilities == 1 || expDim (undefined::Exp aenv sh) > 0
  = mkFold' aenv f z a

  -- Parallel foldAll
  | otherwise
  = mkFoldAll' aenv f z a


-- Reduce an array along the innermost dimension. The innermost dimension must
-- not be empty.
--
mkFold1
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold1 aenv f a
  -- Either (1) multidimensional fold; or
  --        (2) only using one CPU, so just execute sequentially
  | numCapabilities == 1 || expDim (undefined::Exp aenv sh) > 0
  = mkFold1' aenv f a

  -- Parallel foldAll
  | otherwise
  = mkFold1All' aenv f a


-- Multidimensional reduction
-- --------------------------

-- Reduce a multidimensional array. Threads sequentially reduce along the
-- innermost dimensions, so don't need to communicate. Each thread is given a
-- range of innermost dimensions to iterate over, given by [start,end).
--
-- > fold start end = iter start (start * n)
-- >   where
-- >     iter sh sz
-- >       | sh >= end       = return ()
-- >       | otherwise       = do
-- >           let next = sz + n
-- >           writeArray out sh (reduce indexArray c z sz next)
-- >           iter (sh+1) next
--
mkFold'
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold' aenv combine seed IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayDataOp (undefined::Array sh e) "out"
      paramOut                  = arrayParam  (undefined::Array sh e) "out"
      intType                   = typeOf (integralType :: IntegralType Int)
      paramStride               = [Parameter intType "ix.stride" []]

      n                         = local intType "ix.stride"     -- innermost dimension; length to reduce over
      x                         = locals (undefined::e) "x"
      y                         = locals (undefined::e) "y"
      i                         = local intType "i"
      sh                        = local intType "sh"
  in
  makeKernelQ "fold" [llgM|
    define void @fold
    (
        $params:paramGang,
        $params:paramStride,
        $params:paramOut,
        $params:paramEnv
    )
    {
          %sz = mul $type:intType $opr:start, $opr:n

        loop:
          for $type:intType %sh in $opr:start to $opr:end
          {
              %next = add $type:intType %sz, $opr:n
              $bbsM:(x .=. seed)

            reduce:
              for $type:intType %i in %sz to %next
              {
                  $bbsM:(y .=. delayedLinearIndex [i])
                  $bbsM:(x .=. combine x y)
              }

              $bbsM:(writeArray arrOut sh x)
              %sz = $type:intType %next
          }
          ret void
      }
  |]


-- Reduce a non-empty array to a single element. Since there is no seed element
-- provided, initialise the loop accumulator with the first element of the
-- array.
--
mkFold1'
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold1' aenv combine IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayDataOp (undefined::Array sh e) "out"
      paramOut                  = arrayParam  (undefined::Array sh e) "out"
      paramStride               = [Parameter (typeOf (integralType :: IntegralType Int)) "ix.stride" []]

      n                         = local intType "ix.stride"
      intType                   = typeOf (integralType :: IntegralType Int)

      sz                        = local intType "sz"
      sh                        = local intType "sh"
      j                         = local intType "j"
      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"

  in
  makeKernelQ "fold" [llgM|
    define void @fold
    (
        $params:paramGang,
        $params:paramStride,
        $params:paramOut,
        $params:paramEnv
    )
    {     %sz = mul $type:intType $opr:start, $opr:n

          for $type:intType %sh in $opr:start to $opr:end
          {
              %next = add $type:intType %sz, $opr:n
              $bbsM:(acc .=. delayedLinearIndex [sz])
              %start = add $type:intType %sz, 1

            reduce:
              for $type:intType %j in %start to %next
              {
                  $bbsM:(x .=. delayedLinearIndex [j])
                  $bbsM:(acc .=. combine acc x)
              }

              $bbsM:(writeArray arrOut sh acc)
              %sz = $type:intType %next
          }

          ret void
    }
  |]


-- Reduction to scalar
-- -------------------

-- Reduce an array to a single element, with all threads cooperating.
--
-- Since reductions consume arrays that have been fused into them, fold in a
-- multi-threaded context requires two passes. At an example, take vector
-- dot-product:
--
-- > dotp xs ys = fold (+) 0 (zipWith (*) xs ys)
--
--   1. The first pass reads in the fused array data, in this case corresponding
--   to the function (\i -> (xs!i) * (ys!i)).
--
--   2. The second pass just reads the manifest data from the first step
--   directly and reduces the array. This second step is just done by a single
--   thread.
--
mkFoldAll'
    :: forall t aenv sh e. (Shape sh, Elt e)    -- really have sh ~ Z
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFoldAll' aenv combine seed IRDelayed{..} =
  let
      -- inputs
      (start, end, paramGang)   = gangParam
      (tid, paramId)            = gangId
      paramEnv                  = envParam aenv

      -- intermediate result of first step
      paramTmp  = arrayParam  (undefined::Vector e) "tmp"
      arrTmp    = arrayDataOp (undefined::Vector e) "tmp"

      -- output array from final step
      paramOut  = arrayParam  (undefined::Scalar e) "out"
      arrOut    = arrayDataOp (undefined::Scalar e) "out"

      ty_acc    = llvmOfTupleType (eltType (undefined::e))
      zero      = constOp (num int 0)

      manifestLinearIndex [i]   = readArray arrTmp i
      manifestLinearIndex _     = $internalError "makeFoldAll" "expected single expression"
  in do
  [k1] <- makeKernel "foldAll" (paramGang ++ paramTmp ++ paramOut ++ paramEnv) $ do
            r <- reduce ty_acc manifestLinearIndex combine seed start end
            writeArray arrOut zero r
            return_
  [k2] <- makeKernel "fold1" (paramGang ++ paramId ++ paramTmp ++ paramEnv) $ do
            r <- reduce1 ty_acc delayedLinearIndex combine start end
            writeArray arrTmp tid r
            return_
  return [k1,k2]


-- Reduce an array to a single element, without a starting value.
--
-- This is just the second phase of the operation, which takes the manifest
-- array of partial summations from each thread and reduces them to a single
-- value.
--
mkFold1All'
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2 aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold1All' aenv combine IRDelayed{..} =
  let
      -- inputs
      (start, end, paramGang)   = gangParam
      (tid, paramId)            = gangId
      paramEnv                  = envParam aenv

      -- intermediate result of first step
      paramTmp  = arrayParam  (undefined::Vector e) "tmp"
      arrTmp    = arrayDataOp (undefined::Vector e) "tmp"

      -- output array from final step
      paramOut  = arrayParam  (undefined::Scalar e) "out"
      arrOut    = arrayDataOp (undefined::Scalar e) "out"

      ty_acc    = llvmOfTupleType (eltType (undefined::e))
      zero      = constOp (num int 0)

      manifestLinearIndex [i]   = readArray arrTmp i
      manifestLinearIndex _     = $internalError "makeFoldAll" "expected single expression"
  in do
  [k1] <- makeKernel "foldAll" (paramGang ++ paramTmp ++ paramOut ++ paramEnv) $ do
            r <- reduce1 ty_acc manifestLinearIndex combine start end
            writeArray arrOut zero r
            return_
  [k2] <- makeKernel "fold1" (paramGang ++ paramId ++ paramTmp ++ paramEnv) $ do
            r <- reduce1 ty_acc delayedLinearIndex combine start end
            writeArray arrTmp tid r
            return_
  return [k1,k2]


-- Segmented Reduction
-- -------------------
mkFoldSeg
    :: forall t sh e i aenv. (Shape sh, Elt e, Elt i, IsIntegral i)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> IRDelayed aenv (Segments i)
    -> CodeGen [Kernel t aenv (Array (sh:.Int) e)]
mkFoldSeg aenv combine seed arr segs =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramStride               = [Parameter (typeOf (integralType :: IntegralType Int)) "ix.stride" []]
      arrOut                    = arrayDataOp (undefined::Array (sh:.Int) e) "out"
      paramOut                  = arrayParam  (undefined::Array (sh:.Int) e) "out"
      intType                   = typeOf (integralType :: IntegralType Int)

      segT                      = integralType :: IntegralType i
      segType                   = typeOf segT

      n                         = local intType "ix.stride"
      acc                       = locals (undefined::e) "acc"
      y                         = locals (undefined::e) "y"
      i                         = local intType "i"
      j                         = local intType "j"
      k                         = local intType "k"
      l_                        = local segType "l_"
      l                         = local intType "l"
      k1                        = local intType "k1"
      sz                        = local intType "sz"
      segStart                  = local segType "segStart"
      segEnd                    = local segType "segEnd"
  in
  makeKernelQ "foldSeg" [llgM|
    define void @foldSeg
    (
        $params:paramGang,
        $params:paramStride,
        $params:paramOut,
        $params:paramEnv
    )
    {
          $bbsM:([sz] .=. delayedExtent segs)
          %sz_ = sub $type:intType %sz, 1

        loop:
          for $type:intType %j in $opr:start to $opr:end
          {
              %k   = urem $type:intType %j, %sz_
              %k1  = add  $type:intType %k, 1

              $bbsM:(acc .=. seed)
              $bbsM:([segStart] .=. delayedLinearIndex segs [k])
              $bbsM:([segEnd]   .=. delayedLinearIndex segs [k1])

            reduce:
              for $type:segType %l_ in %segStart to %segEnd
              {
                  $bbsM:(l .=. fromIntegral segT int l_)
                  %i_  = udiv $type:intType %j, %sz_
                  %i__ = mul $type:intType %i_, $opr:n
                  %i   = add $type:intType %i__, %l
                  $bbsM:(y .=. delayedLinearIndex arr [i])
                  $bbsM:(acc .=. combine acc y)
              }

              $bbsM:(writeArray arrOut j acc)
          }
          ret void
      }
  |]


mkFold1Seg
    :: forall t sh e i aenv. (Shape sh, Elt e, Elt i, IsIntegral i)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> IRDelayed aenv (Segments i)
    -> CodeGen [Kernel t aenv (Array (sh:.Int) e)]
mkFold1Seg aenv combine arr segs =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramStride               = [Parameter (typeOf (integralType :: IntegralType Int)) "ix.stride" []]
      arrOut                    = arrayDataOp (undefined::Array (sh:.Int) e) "out"
      paramOut                  = arrayParam  (undefined::Array (sh:.Int) e) "out"
      intType                   = typeOf (integralType :: IntegralType Int)

      segT                      = integralType :: IntegralType i
      segType                   = typeOf segT

      n                         = local intType "ix.stride"
      acc                       = locals (undefined::e) "acc"
      y                         = locals (undefined::e) "y"
      i                         = local intType "i"
      j                         = local intType "j"
      k                         = local intType "k"
      l_                        = local segType "l_"
      l                         = local intType "l"
      k1                        = local intType "k1"
      sz                        = local intType "sz"
      segStart                  = local segType "segStart"
      segEnd                    = local segType "segEnd"
  in
  makeKernelQ "fold1Seg" [llgM|
    define void @fold1Seg
    (
        $params:paramGang,
        $params:paramStride,
        $params:paramOut,
        $params:paramEnv
    )
    {
          $bbsM:([sz] .=. delayedExtent segs)
          %sz_ = sub $type:intType %sz, 1

        loop:
          for $type:intType %j in $opr:start to $opr:end
          {
              %k   = srem $type:intType %j, %sz_
              %k1  = add  $type:intType %k, 1

              $bbsM:([segStart] .=. delayedLinearIndex segs [k])
              $bbsM:([segEnd]   .=. delayedLinearIndex segs [k1])
              $bbsM:(l .=. fromIntegral segT int segStart)
              %i_  = udiv $type:intType %j, %sz_
              %i__ = mul $type:intType %i_, $opr:n
              %i  = add $type:intType %i__, %l
              $bbsM:(acc .=. delayedLinearIndex arr [i])

              %segStart1 = add $type:segType %segStart, 1

            reduce:
              for $type:segType %l_ in %segStart1 to %segEnd
              {
                  $bbsM:(l .=. fromIntegral segT int l_)
                  %i = add $type:intType %i__, %l
                  $bbsM:(y .=. delayedLinearIndex arr [i])
                  $bbsM:(acc .=. combine acc y)
              }

              $bbsM:(writeArray arrOut j acc)
          }
          ret void
      }
  |]


-- Reduction loops
-- ---------------

-- Sequentially reduce all elements between the start and end indices, using the
-- provided seed element, combination function, and function to retrieve each
-- element.
--
-- > reduce indexArray c z start end = iter start z
-- >   where
-- >     iter i acc
-- >       | i >= end        = acc
-- >       | otherwise       = iter (i+1) (acc `c` indexArray i)
--
reduce :: [Type]                                        -- Type of the accumulator
       -> ([Operand] -> CodeGen [Operand])              -- read an element of the array
       -> ([Operand] -> [Operand] -> CodeGen [Operand]) -- combine elements
       -> CodeGen [Operand]                             -- seed
       -> Operand                                       -- starting array index
       -> Operand                                       -- final index
       -> CodeGen [Operand]                             -- reduction
reduce ty get combine seed start end = do
  z <- seed
  iterFromTo start end ty z $ \i acc -> combine acc =<< get [i]


-- Sequential reduction loop over a non-empty sequence. The condition is not
-- checked.
--
reduce1 :: [Type]
        -> ([Operand] -> CodeGen [Operand])              -- read an element of the array
        -> ([Operand] -> [Operand] -> CodeGen [Operand]) -- combine elements
        -> Operand                                       -- starting array index
        -> Operand                                       -- final index
        -> CodeGen [Operand]                             -- reduction
reduce1 ty get combine start end = do
  start' <- add int start (constOp $ num int 1)
  reduce ty get combine (get [start]) start' end

