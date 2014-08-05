{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ParallelListComp    #-}
module Data.Array.Accelerate.LLVM.CodeGen.Stencil where

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

--import Data.Array.Accelerate.LLVM.Native.CodeGen.Base

-- standard library
import Control.Monad
import Data.Proxy

stencilAccess
  :: forall a b sh aenv stencil. (Shape sh, Stencil sh a stencil)
  => Proxy (stencil,a)
  -> Proxy sh
  -> [Operand]
  -> [Operand]
  -> Boundary (IRExp aenv a)
  -> IRFun1 aenv (sh -> stencil)
stencilAccess _ _ sh arr bndy ix = do
  let off     = offsets (undefined :: Fun aenv (stencil -> a))
                        (undefined :: OpenAcc aenv (Array sh a))
      off'    = map (reverse . shapeToList) off
  stencil <- mapM (access bndy sh ix arr) off'
  return $ concat stencil

access
  :: Boundary (IRExp aenv e)
  -> [Operand]
  -> [Operand]
  -> [Operand]
  -> [Int]
  -> CodeGen [Operand]
access bndy sh ix arr off =
  if all (==0) off
    then do
      i <- intOfIndex sh ix
      readArray arr i
    else do
      ix' <- zipWithM (add int . (constOp . num int)) off ix
      let op = case bndy of
            Constant as -> Left as
            Clamp       -> Right clamp
            Mirror      -> Right mirror
            Wrap        -> Right wrap
      case op of
        Left as -> do
          as'       <- as
          c         <- inRange sh ix'
          ix''      <- wrap sh ix'
          i         <- intOfIndex sh ix''
          xs        <- readArray arr i
          zipWithM (\a x -> instr (typeOfOperand a) $ Select c x a []) as' xs
        Right op' -> do
          ix'' <- op' sh ix'
          i <- intOfIndex sh ix''
          readArray arr i


-- Test whether an index lies within the boundaries of a shape (first argument)
--
inRange :: [Operand] -> [Operand] -> CodeGen Operand
inRange = f (constOp (nonnum bool True))
  where
    bool = nonNumType :: NonNumType Bool

    f x []      []     = return x
    f x (sz:sh) (i:ix) = do
      c1 <- A.gte int i $ constOp (num int 0)
      c2 <- A.lt int i sz
      c3 <- instr (typeOf bool) $ And c1 c2 []
      c4 <- instr (typeOf bool) $ And x c3 []
      f c4 sh ix
    f _ _ _ = $internalError "inRange" "length of shape and index don't match"

-- Clamp an index to the boundary of the shape (first argument)
--
clamp :: [Operand] -> [Operand] -> CodeGen [Operand]
clamp = zipWithM f
  where
    f sz i = do
      sz' <- A.sub int sz $ constOp (num int 1)
      i' <- A.min int i sz'
      A.max int i' $ constOp (num int 0)

-- Indices out of bounds of the shape are mirrored back in range. Assumes that
-- the array is at least as large as the stencil.
--
mirror :: [Operand] -> [Operand] -> CodeGen [Operand]
mirror = zipWithM f
  where
    f sz i = do
      let intType = typeOf (int::IntegralType Int)
      c1 <- A.gte int i $ constOp (num int 0)
      l <- A.sub int (constOp (num int 0)) i
      i' <- instr intType $ Select c1 i l []
      u <- A.sub int sz =<< A.sub int i' =<< A.sub int sz (constOp (num int 2))
      c2 <- A.lt int i sz
      instr intType $ Select c2 i' u []

-- Indices out of bounds are wrapped to the opposite edge of the shape
--
wrap :: [Operand] -> [Operand] -> CodeGen [Operand]
wrap = zipWithM f
  where
    f sz i = do
      A.mod int i sz
