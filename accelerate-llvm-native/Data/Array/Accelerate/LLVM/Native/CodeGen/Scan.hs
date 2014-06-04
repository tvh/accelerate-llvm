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

  mkScanl1,
  mkScanr1

) where

-- llvm-general
import LLVM.General.AST
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base

-- standard library
import Control.Monad


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

      arrTmp            = arrayData  (undefined::Vector e) "tmp"
      shTmp             = arrayShape (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return (map local shTmp)
        , delayedLinearIndex = readArray arrTmp . single <=< toIRExp
        , delayedIndex       = $internalError "mkScanl1" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanl1Seq aenv f a
  [k2] <- mkScanl1Pre aenv f a
  [k3] <- mkScanl1Post aenv f a tmp
  return [k1,k2,k3]


-- Sequential inclusive left scan
--
mkScanl1Seq
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanl1Seq aenv combine IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayData  (undefined::Vector e) "out"
      paramOut                  = arrayParam (undefined::Vector e) "out"
      intType                   = typeOf (integralType :: IntegralType Int)

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
  in
  makeKernelQ "scanl1Seq" [llgM|
    define void @scanl1Seq
    (
        $params:paramGang,
        $params:paramOut,
        $params:paramEnv
    )
    {
        $bbsM:("x" .=. delayedLinearIndex ([start]))
        $bbsM:(exec  $ writeArray arrOut start ("x" :: Name))
        %start1 = add $type:intType $opr:start, 1
        br label %for

        for:
          for $type:intType %i in %start1 to $opr:end with $types:ty_acc %x as %acc
          {
              $bbsM:("y" .=. delayedLinearIndex ("i" :: [Operand]))
              $bbsM:("z" .=. (combine ("acc" :: Name) ("y" :: Name)))
              $bbsM:(exec    $ writeArray arrOut "i" ("z" :: Name))
              $bbsM:(execRet $ return "z")
          }
          ret void
    }
  |]


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
      arrTmp                    = arrayData  (undefined::Vector e) "tmp"
      paramTmp                  = arrayParam (undefined::Vector e) "tmp"
      intType                   = typeOf (integralType :: IntegralType Int)

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
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
            br label %nextblock

            $bbsM:("x" .=. delayedLinearIndex ("ix" :: [Operand]))
            br label %reduce

          reduce:
            for $type:intType %j in %start1 to %last with $types:ty_acc %x as %acc
            {
                $bbsM:("y" .=. delayedLinearIndex ("j" :: [Operand]))
                $bbsM:("z" .=. (combine ("acc" :: Name) ("y" :: Name)))
                $bbsM:(execRet $ return "z")
            }
            $bbsM:(execRet_ $ writeArray arrTmp "i" ("acc" :: Name))
        }
        ret void
    }
  |]


mkScanl1Post
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanl1Post aenv combine inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam (undefined::Vector e) "tmp"
      arrOut                    = arrayData  (undefined::Vector e) "out"
      paramOut                  = arrayParam (undefined::Vector e) "out"
      intType                   = (typeOf (integralType :: IntegralType Int))

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
  in
  makeKernelQ "scanl1Post" [llgM|
    define void @scanl1Post
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
            br label %nextblock

            ;; sum up the partial sums to get the first element
            $bbsM:("x1" .=. delayedLinearIndex inD ("ix" :: [Operand]))

            for $type:intType %k in 0 to %i with $types:ty_acc %x1 as %x
            {
                %i1 = sub $type:(intType) %i, 1
                br label %nextblock

                $bbsM:("a" .=. delayedLinearIndex tmpD ("i1" :: [Operand]))
                $bbsM:("b" .=. combine ("x" :: Name) ("a" :: Name))
                $bbsM:(execRet $ return "b")
            }
            $bbsM:(exec $ writeArray arrOut "ix" ("x" :: Name))

            %start1 = add $type:(intType) %ix, 1
            br label %reduce

          reduce:
            for $type:intType %j in %start1 to %last with $types:ty_acc %x as %acc
            {
                $bbsM:("y" .=. delayedLinearIndex inD ("j" :: [Operand]))
                $bbsM:("z" .=. (combine ("acc" :: Name) ("y" :: Name)))
                $bbsM:(exec    $ writeArray arrOut "j" ("z" :: Name))
                $bbsM:(execRet $ return "z")
            }
            ret void
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

      arrTmp            = arrayData  (undefined::Vector e) "tmp"
      shTmp             = arrayShape (undefined::Vector e) "tmp"
      tmp               = IRDelayed {
          delayedExtent      = return (map local shTmp)
        , delayedLinearIndex = readArray arrTmp . single <=< toIRExp
        , delayedIndex       = $internalError "mkScanr1" "linear indexing of temporary array only"
        }
  in do
  [k1] <- mkScanr1Seq aenv f a
  [k2] <- mkScanr1Pre aenv f a
  [k3] <- mkScanr1Post aenv f a tmp
  return [k1,k2,k3]


-- Sequential inclusive right scan
--
mkScanr1Seq
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanr1Seq aenv combine IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayData  (undefined::Vector e) "out"
      paramOut                  = arrayParam (undefined::Vector e) "out"
      intType                   = typeOf (integralType :: IntegralType Int)

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
  in
  makeKernelQ "scanr1Seq" [llgM|
    define void @scanl1Seq
    (
        $params:paramGang,
        $params:paramOut,
        $params:paramEnv
    )
    {
        $bbsM:("x" .=. delayedLinearIndex ([start]))
        $bbsM:(exec  $ writeArray arrOut start ("x" :: Name))
        %start1 = sub $type:intType $opr:start, 1
        br label %for

        for:
          for $type:intType %i in %start1 downto $opr:end with $types:ty_acc %x as %acc
          {
              $bbsM:("y" .=. delayedLinearIndex ("i" :: [Operand]))
              $bbsM:("z" .=. (combine ("acc" :: Name) ("y" :: Name)))
              $bbsM:(exec    $ writeArray arrOut "i" ("z" :: Name))
              $bbsM:(execRet $ return "z")
          }
          ret void
    }
  |]


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
      arrTmp                    = arrayData  (undefined::Vector e) "tmp"
      paramTmp                  = arrayParam (undefined::Vector e) "tmp"
      intType                   = typeOf (integralType :: IntegralType Int)

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
  in
  makeKernelQ "scanr1Pre" [llgM|
    define void @scanl1Pre
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
            br label %nextblock

            $bbsM:("x" .=. delayedLinearIndex ("ix" :: [Operand]))
            br label %reduce

          reduce:
            for $type:intType %j in %start1 downto %last with $types:ty_acc %x as %acc
            {
                $bbsM:("y" .=. delayedLinearIndex ("j" :: [Operand]))
                $bbsM:("z" .=. (combine ("acc" :: Name) ("y" :: Name)))
                $bbsM:(execRet $ return "z")
            }
            $bbsM:(execRet_ $ writeArray arrTmp "i" ("acc" :: Name))
        }
        ret void
    }
  |]


mkScanr1Post
    :: forall t aenv e. (Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Vector e)
    -> IRDelayed aenv (Vector e)
    -> CodeGen [Kernel t aenv (Vector e)]
mkScanr1Post aenv combine inD tmpD =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      paramTmp                  = arrayParam (undefined::Vector e) "tmp"
      arrOut                    = arrayData  (undefined::Vector e) "out"
      paramOut                  = arrayParam (undefined::Vector e) "out"
      intType                   = (typeOf (integralType :: IntegralType Int))

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
  in
  makeKernelQ "scanr1Post" [llgM|
    define void @scanl1Post
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
            %ix_   = mul $type:intType %i,  %chunkSize
            %ix    = sub $type:intType %sz, %ix_
            %last1 = sub $type:intType %ix, %chunkSize
            %c1    = icmp eq $type:intType %i, %lastChunk
            %last  = select i1 %c1, $type:intType -1, $type:intType %last1
            br label %nextblock

            ;; sum up the partial sums to get the first element
            $bbsM:("x1" .=. delayedLinearIndex inD ("ix" :: [Operand]))

            for $type:intType %k in 0 to %i with $types:ty_acc %x1 as %x
            {
                %i1 = sub $type:(intType) %i, 1
                br label %nextblock

                $bbsM:("a" .=. delayedLinearIndex tmpD ("i1" :: [Operand]))
                $bbsM:("b" .=. combine ("x" :: Name) ("a" :: Name))
                $bbsM:(execRet $ return "b")
            }
            $bbsM:(exec $ writeArray arrOut "ix" ("x" :: Name))

            %start1 = sub $type:(intType) %ix, 1
            br label %reduce

          reduce:
            for $type:intType %j in %start1 downto %last with $types:ty_acc %x as %acc
            {
                $bbsM:("y" .=. delayedLinearIndex inD ("j" :: [Operand]))
                $bbsM:("z" .=. (combine ("acc" :: Name) ("y" :: Name)))
                $bbsM:(exec    $ writeArray arrOut "j" ("z" :: Name))
                $bbsM:(execRet $ return "z")
            }
            ret void
        }
        ret void
    }
  |]

