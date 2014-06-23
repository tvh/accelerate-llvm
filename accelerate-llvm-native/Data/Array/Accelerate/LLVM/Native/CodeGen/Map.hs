{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Map
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Map
  where

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array, Elt )

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base

import LLVM.General.Quote.LLVM
import Data.Array.Accelerate.Type

-- C Code
-- ======
--
-- float f(float);
--
-- void map(float* __restrict__ out, const float* __restrict__ in, const int n)
-- {
--     for (int i = 0; i < n; ++i)
--         out[i] = f(in[i]);
--
--     return;
-- }

-- Corresponding LLVM
-- ==================
--
-- define void @map(float* noalias nocapture %out, float* noalias nocapture %in, i32 %n) nounwind uwtable ssp {
--   %1 = icmp sgt i32 %n, 0
--   br i1 %1, label %.lr.ph, label %._crit_edge
--
-- .lr.ph:                                           ; preds = %0, %.lr.ph
--   %indvars.iv = phi i64 [ %indvars.iv.next, %.lr.ph ], [ 0, %0 ]
--   %2 = getelementptr inbounds float* %in, i64 %indvars.iv
--   %3 = load float* %2, align 4
--   %4 = tail call float @apply(float %3) nounwind
--   %5 = getelementptr inbounds float* %out, i64 %indvars.iv
--   store float %4, float* %5, align 4
--   %indvars.iv.next = add i64 %indvars.iv, 1
--   %lftr.wideiv = trunc i64 %indvars.iv.next to i32
--   %exitcond = icmp eq i32 %lftr.wideiv, %n
--   br i1 %exitcond, label %._crit_edge, label %.lr.ph
--
-- ._crit_edge:                                      ; preds = %.lr.ph, %0
--   ret void
-- }
--
-- declare float @apply(float)
--


-- Apply the given unary function to each element of an array.
--
mkMap :: forall t aenv sh a b. (Elt b, Elt a)
      => Gamma aenv
      -> IRFun1    aenv (a -> b)
      -> IRDelayed aenv (Array sh a)
      -> CodeGen [Kernel t aenv (Array sh b)]
mkMap aenv apply IRDelayed{..} =
  let (start, end, paramGang)   = gangParam
      arrOut                    = arrayDataOp  (undefined::Array sh b) "out"
      paramOut                  = arrayParam (undefined::Array sh b) "out"
      paramEnv                  = envParam aenv
      intType                   = typeOf (integralType :: IntegralType Int)

      x                         = locals (undefined::a) "x"
      y                         = locals (undefined::b) "y"
      i                         = local intType "i"
  in
  makeKernelQ "map" [llgM|
    define void @map
    (
        $params:paramGang,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:(x .=. delayedLinearIndex [i])
            $bbsM:(y .=. apply x)
            $bbsM:(writeArray arrOut i y)
        }
        ret void
    }
  |]

