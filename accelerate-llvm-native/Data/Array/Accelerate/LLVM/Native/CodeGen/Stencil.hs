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

  mkStencil

) where

-- llvm-general
import LLVM.General.AST
import LLVM.General.AST.Constant ( Constant( Int ) )
import LLVM.General.Quote.LLVM

-- accelerate
import Data.Array.Accelerate.Analysis.Stencil
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST ( Fun, OpenAcc, Stencil )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Smart hiding ( Stencil )
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base

-- standard library
import Control.Monad

mkStencil
  :: forall arch aenv sh stencil a b. (Elt a, Elt b, Stencil sh a stencil)
  => Gamma aenv
  -> stencil
  -> IRFun1 aenv (stencil -> b)
  -> Boundary (IRExp aenv a)
  -> IRDelayed aenv (Array sh a)
  -> CodeGen [Kernel arch aenv (Array sh b)]
mkStencil aenv stencil apply bndy delayed =
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayData  (undefined::Array sh b) "out"
      paramOut                  = arrayParam (undefined::Array sh b) "out"
      intType                   = typeOf (integralType :: IntegralType Int)

  in
  makeKernelQ "stencil" [llgM|
    define void @stencil
    (
        $params:paramGang,
        $params:paramOut,
        $params:paramEnv
    )
    {
        for $type:intType %i in $opr:start to $opr:end
        {
            $bbsM:("x" .=. stencilAccess stencil delayed bndy ("i" :: [Operand]))
            $bbsM:("y" .=. apply ("x" :: Name))
            $bbsM:(writeArray arrOut "i" ("y" :: Name))
        }
        ret void
    }
  |]



stencilAccess 
  :: forall a sh aenv stencil. (Shape sh, Stencil sh a stencil)
  => stencil
  -> IRDelayed aenv (Array sh a)
  -> Boundary (IRExp aenv a)
  -> IRFun1 aenv (Int -> stencil)
stencilAccess stencil IRDelayed{..} bndy index' = do
  let intBits = typeBits $ typeOf (integralType :: IntegralType Int)
      off     = offsets (undefined :: Fun aenv (stencil -> a))
                        (undefined :: OpenAcc aenv (Array sh a))
      off'    = map shapeToList off
  [linearIndex] <- toIRExp index'
  sh <- delayedExtent
  ix <- indexOfInt sh linearIndex
  indices <- mapM (access bndy sh ix) off'
  values <- mapM delayedIndex indices
  return $ concat indices

access
  :: Boundary (IRExp aenv e)
  -> [Operand]
  -> [Operand]
  -> [Int]
  -> CodeGen [Operand]
access bndy sh ix off = do
  let off' = map (constOp . num int) off
  cursor <- intOfIndex sh ix
  ix' <- zipWithM (add int) ix off'
  case bndy of
    Clamp -> clamp sh ix'
    


-- Clamp an index to the boundary of the shape (first argument)
--
clamp :: [Operand] -> [Operand] -> CodeGen [Operand]
clamp = zipWithM f
  where
    f sz i = do
      u <- A.min int i sz
      A.max int u $ constOp (num int 0)

