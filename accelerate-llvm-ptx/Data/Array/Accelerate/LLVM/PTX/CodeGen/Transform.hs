{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Transform
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Transform
  where

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array, Shape, Elt )

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.PTX.Target                    ( PTX )
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop

-- standard library
import Prelude                                                  hiding ( fromIntegral )


-- A combination map/backpermute, where the index and value transformations have
-- been separated
--
mkTransform
    :: forall t aenv sh sh' a b. (Shape sh, Shape sh', Elt a, Elt b)
    => PTX
    -> Gamma aenv
    -> IRFun1    aenv (sh' -> sh)
    -> IRFun1    aenv (a -> b)
    -> IRDelayed aenv (Array sh a)
    -> CodeGen [Kernel t aenv (Array sh' b)]
mkTransform _dev aenv permute apply IRDelayed{..} =
  let
      (start, end, paramGang)   = gangParam
      arrOut                    = arrayData  (undefined::Array sh' b) "out"
      shOut                     = arrayShape (undefined::Array sh' b) "out"
      paramOut                  = arrayParam (undefined::Array sh' b) "out"
      paramEnv                  = envParam aenv
  in
  makeKernel "transform" (paramGang ++ paramOut ++ paramEnv) $ do

    imapFromTo start end $ \i -> do
      ii  <- fromIntegral int32 int i           -- loop counter is i32, calculation is in Int
      ix  <- indexOfInt shOut ii                -- convert to multidimensional index
      ix' <- permute ix                         -- apply backwards index permutation
      xs  <- delayedIndex ix'                   -- get element
      ys  <- apply xs                           -- apply function from input array
      writeArray arrOut i ys

    return_

