{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE QuasiQuotes         #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Permute
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Permute
  where

-- llvm-general
import LLVM.General.AST
import LLVM.General.AST.RMWOperation
import LLVM.General.AST.Type (ptr)
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Sugar                                ( Array, Vector, Shape, Elt )
import qualified Data.Array.Accelerate.Array.Sugar                      as Sugar

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                    as A hiding ( fromIntegral )
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
import Prelude                                                          hiding ( all )
import Control.Monad
import qualified Foreign.Storable                                       as S


-- A forward permutation is specified by an index mapping that determines, for
-- each element in the source array, where it should go in the target array. The
-- resultant array is initialised with the given defaults and any further values
-- that are permuted into the result array are added to the current value using
-- the given combination function.
--
-- The combination function must be associative. Elements that are mapped to the
-- magic value 'ignore' by the permutation function are dropped.
--
--   permute :: (Shape sh, Shape sh', Elt a)
--           => (Exp a -> Exp a -> Exp a)               -- combination function
--           -> Acc (Array sh' a)                       -- array of default values (manifest)
--           -> (Exp sh -> Exp sh')                     -- forward permutation
--           -> Acc (Array sh  a)                       -- array to be permuted (delayed)
--           -> Acc (Array sh' a)
--
mkPermute
    :: forall arch aenv sh sh' e. (Shape sh, Shape sh', Elt e)
    => Gamma aenv
    -> IRFun2 aenv (e -> e -> e)
    -> IRFun1 aenv (sh -> sh')
    -> IRDelayed aenv (Array sh e)
    -> CodeGen [Kernel arch aenv (Array sh' e)]
mkPermute aenv combine permute IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      arrOut                    = arrayDataOp  (undefined::Array sh' e) "out"
      shOut                     = arrayShapeOp (undefined::Array sh' e) "out"
      paramOut                  = arrayParam   (undefined::Array sh' e) "out"
      paramEnv                  = envParam aenv
      intType                   = typeOf (integralType :: IntegralType Int)
      i1                        = typeOf (scalarType :: ScalarType Bool)

      shIn                      = arrayShapeOp (undefined::Array sh e) ""

      ignore                    = map (constOp . integral integralType)
                                $ Sugar.shapeToList (Sugar.ignore :: sh')

      [barrier]                 = arrayDataOp (undefined::Vector Word8) "barrier"
      paramBarrier              = arrayParam (undefined::Vector Word8) "barrier"

      i                         = local intType "i"
      ix                        = locals (undefined::sh) "ix"
      ix'                       = locals (undefined::sh) "ix'"
      c1                        = local i1 "c1"
      dst                       = local intType "dst"
      old                       = locals (undefined::e) "old"
      new                       = locals (undefined::e) "new"
      val                       = locals (undefined::e) "val"
  in
  makeKernelQ "permute" [llgM|
    define void @permute
    (
        $params:paramGang,
        $params:paramBarrier,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:(ix .=. indexOfInt shOut i)          ;; convert to multidimensional index
            $bbsM:(ix' .=. permute ix)                 ;; apply index permutation

            ;; If this index will not be used, jump immediately to the exit
            $bbsM:(c1 .=. all (uncurry (neq int)) (zip ix' ignore))
            if %c1 {
                $bbsM:(dst .=. intOfIndex shOut ix')   ;; index of result array

                ;; The thread spins waiting for this slot of the output array to become
                ;; unlocked. The thread spins waiting for the lock to be released, which is the
                ;; worst possible setup in a highly contented environment.
                ;;
                ;; However, since the thread attempts to acquire the lock in a loop without
                ;; trying to write anything until the value changes, because of MESI caching
                ;; protocols this should cause the cache line the lock is on to become "Shared".
                ;; If this is the case, then there is remarkably _no_ bus traffic while the CPU
                ;; waits for the lock. This optimisation is effective on all CPU architectures
                ;; that have a cache per CPU.
                %baddr = getelementptr i8* $opr:barrier, $type:intType $opr:dst
                %c2 = i1 true
                while %c2 {
                    ;; Atomically set the slot to the locked state, returning the old state. If
                    ;; the slot was unlocked we just acquired it, otherwise the state remains
                    ;; unchanged (previously locked) and we need to spin until it becomes
                    ;; unlocked.
                    %lock = atomicrmw volatile xchg i8* %baddr, i8 1 acquire
                    %c2 = icmp eq i8 %lock, 0
                }

                $bbsM:(old .=. readArray arrOut dst)
                $bbsM:(new .=. delayedLinearIndex [i])
                $bbsM:(val .=. combine new old)
                $bbsM:(writeArray arrOut dst val)

                ;; Later x86 architectures can release the lock safely by using an unlocked
                ;; MOV instruction rather than the slower locked XCHG. This is due to subtle
                ;; memory ordering rules which allow this, even though MOV is not a full
                ;; memory barrier.
                store atomic volatile i8 0, i8* %baddr release, align 1
            }
        }
        ret void
    }|]


-- Apply the function (f :: a -> Bool) to each argument. If any application
-- returns false, return false. Otherwise return true.
--
all :: (a -> CodeGen Operand) -> [a] -> CodeGen Operand
all = go true
  where
    i1 = scalarType :: ScalarType Bool

    true :: Operand
    true = constOp $ scalar i1 True

    go :: Operand -> (a -> CodeGen Operand) -> [a] -> CodeGen Operand
    go b _ []     = return b
    go b f (x:xs) = do
      x' <- f x
      b' <- land b x'
      go b' f xs
