{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Transform
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Transform
  where

-- llvm-general
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array, Shape, Elt )
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base


-- A combination map/backpermute, where the index and value transformations have
-- been separated
--
mkTransform
    :: forall t aenv sh sh' a b. (Shape sh, Shape sh', Elt a, Elt b)
    => Gamma aenv
    -> IRFun1    aenv (sh' -> sh)
    -> IRFun1    aenv (a -> b)
    -> IRDelayed aenv (Array sh a)
    -> CodeGen [Kernel t aenv (Array sh' b)]
mkTransform aenv permute apply IRDelayed{..} =
  let
      arrOut                    = arrayDataOp  (undefined::Array sh' b) "out"
      shOut                     = arrayShapeOp (undefined::Array sh' b) "out"
      paramOut                  = arrayParam   (undefined::Array sh' b) "out"
      paramEnv                  = envParam aenv
      (start, end, paramGang)   = gangParam
      intType                   = typeOf (integralType :: IntegralType Int)

      i                         = local intType "i"
      ix                        = locals (undefined::sh) "ix"
      ix'                       = locals (undefined::sh') "ix'"
      xs                        = locals (undefined::a) "xs"
      ys                        = locals (undefined::b) "ys"
  in
  makeKernelQ "transform" [llgM|
    define void @transform
    (
        $params:paramGang,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:(ix .=. indexOfInt shOut i)        ;; convert to multidimensional index
            $bbsM:(ix' .=. permute ix)               ;; apply backwards index permutation
            $bbsM:(xs .=. delayedIndex ix')          ;; get element
            $bbsM:(ys .=. apply xs)                  ;; apply function from input array
            $bbsM:(writeArray arrOut i ys)
        }
        ret void
    }
  |]

