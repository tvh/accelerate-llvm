{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE QuasiQuotes         #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
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


-- Construct a new array by applying a function to each index. Each thread
-- processes multiple adjacent elements.
--
mkGenerate
    :: forall arch aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun1 aenv (sh -> e)
    -> CodeGen [Kernel arch aenv (Array sh e)]
mkGenerate aenv apply =
  let
      arrOut                    = arrayDataOp  (undefined::Array sh e) "out"
      shOut                     = arrayShapeOp (undefined::Array sh e) "out"
      paramOut                  = arrayParam   (undefined::Array sh e) "out"
      paramEnv                  = envParam aenv
      (start, end, paramGang)   = gangParam
      intType                   = typeOf (integralType :: IntegralType Int)

      r                         = locals (undefined::e) "r"
      i                         = local intType "i"
      ix                        = locals (undefined::sh) "ix"
  in
  makeKernelQ "generate" [llgM|
    define void @generate
    (
        $params:paramGang,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:(ix .=. indexOfInt shOut i)          ;; convert to multidimensional index
            $bbsM:(r  .=. apply ix)                    ;; apply generator function
            $bbsM:(writeArray arrOut i r)              ;; store result
        }
        ret void
    }
  |]

