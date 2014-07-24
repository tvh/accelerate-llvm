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
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Array.Accelerate.LLVM.Native.CodeGen.Stencil (

  mkStencil,
  mkStencil2

) where

-- llvm-general
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST ( Stencil )
import Data.Array.Accelerate.Smart hiding ( Stencil )
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Stencil
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base

-- standard library
import Data.Proxy

mkStencil
  :: forall arch aenv sh stencil a b. (Elt b, Stencil sh a stencil)
  => Gamma aenv
  -> Proxy (stencil,a)
  -> IRFun1 aenv (stencil -> b)
  -> Boundary (IRExp aenv a)
  -> CodeGen [Kernel arch aenv (Array sh b)]
mkStencil aenv stencilT apply bndy =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayDataOp  (undefined::Array sh b) "out"
      paramOut                  = arrayParam   (undefined::Array sh b) "out"
      shOut                     = arrayShapeOp (undefined::Array sh b) "out"
      arrIn                     = arrayDataOp  (undefined::Array sh a) "in"
      paramIn                   = arrayParam   (undefined::Array sh a) "in"
      shIn                      = arrayShapeOp (undefined::Array sh a) "in"
      intType                   = typeOf (integralType :: IntegralType Int)

      shT                       = Proxy :: Proxy sh

      x                         = locals (undefined::b) "x"
      i                         = local intType "i"
      ix                        = locals (undefined::sh) "ix"
  in
  makeKernelQ "stencil" [llgM|
    define void @stencil
    (
        $params:paramGang,
        $params:paramIn,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:(ix .=. indexOfInt shOut i)
            $bbsM:(x .=. (stencilAccess stencilT shT shIn arrIn bndy ix >>= apply))
            $bbsM:(writeArray arrOut i x)
        }
        ret void
    }
  |]

mkStencil2
  :: forall arch aenv sh stencil1 stencil2 a b c. (Elt c, Stencil sh a stencil1, Stencil sh b stencil2)
  => Gamma aenv
  -> Proxy ((stencil1,a), (stencil2,b))
  -> IRFun2 aenv (stencil1 -> stencil2 -> b)
  -> Boundary (IRExp aenv a)
  -> Boundary (IRExp aenv b)
  -> CodeGen [Kernel arch aenv (Array sh c)]
mkStencil2 aenv _ apply bndy1 bndy2 =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayDataOp  (undefined::Array sh c) "out"
      paramOut                  = arrayParam   (undefined::Array sh c) "out"
      shOut                     = arrayShapeOp (undefined::Array sh c) "out"
      arrIn1                    = arrayDataOp  (undefined::Array sh a) "in1"
      paramIn1                  = arrayParam   (undefined::Array sh a) "in1"
      shIn1                     = arrayShapeOp (undefined::Array sh a) "in1"
      arrIn2                    = arrayDataOp  (undefined::Array sh b) "in2"
      paramIn2                  = arrayParam   (undefined::Array sh b) "in2"
      shIn2                     = arrayShapeOp (undefined::Array sh b) "in2"
      intType                   = typeOf (integralType :: IntegralType Int)

      shT                       = Proxy :: Proxy sh
      stencil1T                 = Proxy :: Proxy (stencil1,a)
      stencil2T                 = Proxy :: Proxy (stencil2,b)

      x                         = locals (undefined::c) "x"
      i                         = local intType "i"
      ix                        = locals (undefined::sh) "ix"
  in
  makeKernelQ "stencil2" [llgM|
    define void @stencil2
    (
        $params:paramGang,
        $params:paramIn1,
        $params:paramIn2,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:(ix .=. indexOfInt shOut i)
            $bbsM:(x .=. (stencilAccess stencil1T shT shIn1 arrIn1 bndy1 ix >>= \a -> stencilAccess stencil2T shT shIn2 arrIn2 bndy2 ix >>= apply a))
            $bbsM:(writeArray arrOut i x)
        }
        ret void
    }
  |]
