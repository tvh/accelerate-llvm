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

module Data.Array.Accelerate.LLVM.Native.CodeGen.Scan (

  mkScanl,
  mkScanr,
  
  mkScanl1,
  mkScanr1,

  mkScanl'

) where

-- llvm-general
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base

import Data.Coerce

-- Inclusive scan, which returns an array of successive reduced values from the
-- left.
--
mkScanl
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanl aenv f s a =
  let
      single [i]        = i
      single _          = $internalError "single" "expected single expression"

      arrTmp            = arrayDataOp  (undefined::Vector e) "tmp"
      shTmp             = arrayShapeOp (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return shTmp
        , delayedLinearIndex = readArray arrTmp . single
        , delayedIndex       = $internalError "mkScanl" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanl1Pre aenv f a
  [k2] <- mkScanlOp aenv f s a tmp
  return [k1,k2]


mkScanlOp
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanlOp aenv combine seed inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      arrOut                    = arrayDataOp (undefined::Vector e) "out"
      paramOut                  = arrayParam  (undefined::Vector e) "out"
      intType                   = (typeOf (integralType :: IntegralType Int))

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      ix                        = local intType "ix"
      k                         = local intType "k"
      k1                        = local intType "k1"
  in
  makeKernelQ "scanl" [llgM|
    define void @scanlPost
    (
        $params:paramGang ,
        $type:intType %lastChunk,
        $type:intType %chunkSize,
        $type:intType %sz,
        $params:paramTmp,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix    = mul $type:intType %i,  %chunkSize
            %last1 = add $type:intType %ix, %chunkSize
            %c1    = icmp eq $type:intType %i, %lastChunk
            %last  = select i1 %c1, $type:intType %sz, $type:intType %last1

            ;; sum up the partial sums to get the first element
            $bbsM:(acc .=. seed)

            for $type:intType %k in 0 to %i
            {
                $bbsM:(x .=. delayedLinearIndex tmpD [k])
                $bbsM:(acc .=. combine x acc)
            }

            ;; check if this is the first chunk
            %c2 = icmp eq $type:intType %ix, 0
            ;; if it is, write the seed to memory
            if %c2 {
              $bbsM:(writeArray arrOut ix acc)
            }

          reduce:
            for $type:intType %k in %ix to %last
            {
                %k1 = add $type:intType %k, 1
                $bbsM:(x .=. delayedLinearIndex inD [k])
                $bbsM:(acc .=. combine acc x)
                $bbsM:(writeArray arrOut k1 acc)
            }
        }
        ret void
    }
  |]


-- Inclusive scan, which returns an array of successive reduced values from the
-- left.
--
mkScanl'
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e, Scalar e)]
mkScanl' aenv f s a =
  let
      single [i]        = i
      single _          = $internalError "single" "expected single expression"

      arrTmp            = arrayDataOp  (undefined::Vector e) "tmp"
      shTmp             = arrayShapeOp (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return shTmp
        , delayedLinearIndex = readArray arrTmp . single
        , delayedIndex       = $internalError "mkScanl'" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanl1Pre aenv f a
  [k2] <- mkScanl'Op aenv f s a tmp
  return [coerce k1,k2]


mkScanl'Op
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e, Scalar e)]
mkScanl'Op aenv combine seed inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      arrOut                    = arrayDataOp (undefined::Vector e) "out"
      paramOut                  = arrayParam  (undefined::Vector e) "out"
      arrLast                   = arrayDataOp (undefined::Vector e) "outLast"
      paramLast                 = arrayParam  (undefined::Vector e) "outLast"
      intType                   = (typeOf (integralType :: IntegralType Int))

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      ix                        = local intType "ix"
      k                         = local intType "k"
      k1                        = local intType "k1"
      sz1                       = local intType "sz1"

      zero                      = constOp $ num int 0
  in
  makeKernelQ "scanl" [llgM|
    define void @scanl
    (
        $params:paramGang ,
        $type:intType %lastChunk,
        $type:intType %chunkSize,
        $type:intType %sz,
        $params:paramTmp,
        $params:paramOut,
        $params:paramLast,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix    = mul $type:intType %i,  %chunkSize
            %last1 = add $type:intType %ix, %chunkSize
            %c1    = icmp eq $type:intType %i, %lastChunk
            %last  = select i1 %c1, $type:intType %sz, $type:intType %last1

            ;; sum up the partial sums to get the first element
            $bbsM:(acc .=. seed)

            for $type:intType %k in 0 to %i
            {
                $bbsM:(x .=. delayedLinearIndex tmpD [k])
                $bbsM:(acc .=. combine x acc)
            }

            ;; check if this is the first chunk
            %c2 = icmp eq $type:intType %ix, 0
            ;; if it is, write the seed to memory
            if %c2 {
                %c3 = icmp ne $type:intType %sz, 0
                if %c3 {
                   $bbsM:(writeArray arrLast zero acc)
                }
            }

          reduce:
            for $type:intType %k in %ix to %last
            {
                %k1 = add $type:intType %k, 1
                $bbsM:(x .=. delayedLinearIndex inD [k])
                $bbsM:(acc .=. combine acc x)
                %c4 = icmp ne $type:intType %k1, %sz
                if %c4 {
                    $bbsM:(writeArray arrOut zero acc)
                }
            }

            ;;write the last element
            if %c1 {
                $bbsM:(writeArray arrLast zero acc)
            }
        }

        ret void
    }
  |]


-- Inclusive scan, which returns an array of successive reduced values from the
-- left.
--
mkScanl1
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanl1 aenv f a =
  let
      single [i]        = i
      single _          = $internalError "single" "expected single expression"

      arrTmp            = arrayDataOp  (undefined::Vector e) "tmp"
      shTmp             = arrayShapeOp (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return shTmp
        , delayedLinearIndex = readArray arrTmp . single
        , delayedIndex       = $internalError "mkScanl1" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanl1Pre aenv f a
  [k2] <- mkScanl1Op aenv f a tmp
  return [k1,k2]


mkScanl1Pre
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanl1Pre aenv combine IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrTmp                    = arrayDataOp (undefined::Vector e) "tmp"
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      intType                   = typeOf (integralType :: IntegralType Int)

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      ix                        = local intType "ix"
      j                         = local intType "j"
      i                         = local intType "i"
  in
  makeKernelQ "scanl1Pre" [llgM|
    define void @scanl1Pre
    (
        $params:paramGang,
        $type:intType %chunkSize,
        $params:paramTmp,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix     = mul $type:(intType) %i,  %chunkSize
            %last   = add $type:(intType) %ix, %chunkSize
            %start1 = add $type:(intType) %ix, 1

            $bbsM:(acc .=. delayedLinearIndex [ix])

          reduce:
            for $type:intType %j in %start1 to %last
            {
                $bbsM:(x .=. delayedLinearIndex [j])
                $bbsM:(acc .=. combine acc x)
            }
            $bbsM:(writeArray arrTmp i acc)
        }
        ret void
    }
  |]


mkScanl1Op
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanl1Op aenv combine inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      arrOut                    = arrayDataOp (undefined::Vector e) "out"
      paramOut                  = arrayParam  (undefined::Vector e) "out"
      intType                   = (typeOf (integralType :: IntegralType Int))

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      ix                        = local intType "ix"
      k                         = local intType "k"
  in
  makeKernelQ "scanl1" [llgM|
    define void @scanl1
    (
        $params:paramGang ,
        $type:intType %lastChunk,
        $type:intType %chunkSize,
        $type:intType %sz,
        $params:paramTmp,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix    = mul $type:intType %i,  %chunkSize
            %last1 = add $type:intType %ix, %chunkSize
            %c1    = icmp eq $type:intType %i, %lastChunk
            %last  = select i1 %c1, $type:intType %sz, $type:intType %last1

            ;; sum up the partial sums to get the first element
            $bbsM:(acc .=. delayedLinearIndex inD [ix])

            for $type:intType %k in 0 to %i
            {
                $bbsM:(x .=. delayedLinearIndex tmpD [k])
                $bbsM:(acc .=. combine x acc)
            }
            $bbsM:(writeArray arrOut ix acc)

            %start1 = add $type:(intType) %ix, 1
            br label %reduce

          reduce:
            for $type:intType %k in %start1 to %last
            {
                $bbsM:(x .=. delayedLinearIndex inD [k])
                $bbsM:(acc .=. combine acc x)
                $bbsM:(writeArray arrOut k acc)
            }
        }
        ret void
    }
  |]

-- Inclusive scan, which returns an array of successive reduced values from the
-- right.
--
mkScanr
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanr aenv f s a =
  let
      single [i]        = i
      single _          = $internalError "single" "expected single expression"

      arrTmp            = arrayDataOp  (undefined::Vector e) "tmp"
      shTmp             = arrayShapeOp (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return shTmp
        , delayedLinearIndex = readArray arrTmp . single
        , delayedIndex       = $internalError "mkScanr" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanr1Pre aenv f a
  [k2] <- mkScanrOp aenv f s a tmp
  return [k1,k2]


mkScanrOp
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanrOp aenv combine seed inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      arrOut                    = arrayDataOp (undefined::Vector e) "out"
      paramOut                  = arrayParam  (undefined::Vector e) "out"
      intType                   = typeOf (integralType :: IntegralType Int)

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      k                         = local intType "k"
      ix1                       = local intType "ix1"
  in
  makeKernelQ "scanr" [llgM|
    define void @scanr
    (
        $params:paramGang ,
        $type:intType %lastChunk,
        $type:intType %chunkSize,
        $type:intType %sz,
        $params:paramTmp,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix_   = mul $type:intType %i,   %chunkSize
            %ix1   = sub $type:intType %sz,  %ix_
            %ix    = sub $type:intType %ix1, 1
            %last_ = sub $type:intType %ix,  %chunkSize
            %c1    = icmp eq $type:intType %i, %lastChunk
            %last  = select i1 %c1, $type:intType -1, $type:intType %last_

            ;; sum up the partial sums to get the first element
            $bbsM:(acc .=. seed)

            for $type:intType %k in 0 to %i
            {
                $bbsM:(x .=. delayedLinearIndex tmpD [k])
                $bbsM:(acc .=. combine acc x)
            }

            ;; check if this is the first chunk
            %c2 = icmp eq $type:intType %i, 0
            if %c2 {
              ;; if it is, then write the seed element
              $bbsM:(exec $ writeArray arrOut ix1 acc)
            }

          reduce:
            for $type:intType %k in %ix downto %last
            {
                $bbsM:(x .=. delayedLinearIndex inD [k])
                $bbsM:(acc .=. combine x acc)
                $bbsM:(writeArray arrOut k acc)
            }
        }
        ret void
    }
  |]

-- Inclusive scan, which returns an array of successive reduced values from the
-- right.
--
mkScanr1
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanr1 aenv f a =
  let
      single [i]        = i
      single _          = $internalError "single" "expected single expression"

      arrTmp            = arrayDataOp  (undefined::Vector e) "tmp"
      shTmp             = arrayShapeOp (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return shTmp
        , delayedLinearIndex = readArray arrTmp . single
        , delayedIndex       = $internalError "mkScanr1" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanr1Pre aenv f a
  [k2] <- mkScanr1Op aenv f a tmp
  return [k1,k2]


mkScanr1Pre
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanr1Pre aenv combine IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrTmp                    = arrayDataOp (undefined::Vector e) "tmp"
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      intType                   = typeOf (integralType :: IntegralType Int)

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      ix                        = local intType "ix"
      i                         = local intType "i"
      k                         = local intType "k"
  in
  makeKernelQ "scanr1Pre" [llgM|
    define void @scanr1Pre
    (
        $params:paramGang,
        $type:intType %chunkSize,
        $type:intType %sz,
        $params:paramTmp,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix_    = mul $type:(intType) %i,  %chunkSize
            %ix     = sub $type:(intType) %sz, %ix_
            %last   = sub $type:(intType) %ix, %chunkSize
            %start1 = sub $type:(intType) %ix, 1

            $bbsM:(acc .=. delayedLinearIndex [ix])

          reduce:
            for $type:intType %k in %start1 downto %last
            {
                $bbsM:(x .=. delayedLinearIndex [k])
                $bbsM:(acc .=. combine acc x)
            }
            $bbsM:(writeArray arrTmp i acc)
        }
        ret void
    }
  |]


mkScanr1Op
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanr1Op aenv combine inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam  (undefined::Vector e) "tmp"
      arrOut                    = arrayDataOp (undefined::Vector e) "out"
      paramOut                  = arrayParam  (undefined::Vector e) "out"
      intType                   = (typeOf (integralType :: IntegralType Int))

      acc                       = locals (undefined::e) "acc"
      x                         = locals (undefined::e) "x"
      ix                        = local intType "ix"
      k                         = local intType "k"
  in
  makeKernelQ "scanr1" [llgM|
    define void @scanr1
    (
        $params:paramGang ,
        $type:intType %lastChunk,
        $type:intType %chunkSize,
        $type:intType %sz,
        $params:paramTmp,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            %ix_   = mul $type:intType %i,   %chunkSize
            %ix1   = sub $type:intType %sz,  %ix_
            %ix    = sub $type:intType %ix1, 1
            %last1 = sub $type:intType %ix,  %chunkSize
            %c1    = icmp eq $type:intType %i, %lastChunk
            %last  = select i1 %c1, $type:intType -1, $type:intType %last1

            ;; sum up the partial sums to get the first element
            $bbsM:(acc .=. delayedLinearIndex inD [ix])

            for $type:intType %k in 0 to %i
            {
                $bbsM:(x .=. delayedLinearIndex tmpD [k])
                $bbsM:(acc .=. combine x acc)
            }
            $bbsM:(writeArray arrOut ix acc)

            %start1 = sub $type:(intType) %ix, 1

          reduce:
            for $type:intType %k in %start1 downto %last
            {
                $bbsM:(x .=. delayedLinearIndex inD [k])
                $bbsM:(acc .=. combine acc x)
                $bbsM:(writeArray arrOut k acc)
            }
        }
        ret void
    }
  |]

