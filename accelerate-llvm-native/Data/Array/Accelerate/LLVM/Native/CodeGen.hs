{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen
  where

-- accelerate
import Data.Array.Accelerate.LLVM.CodeGen

import Data.Array.Accelerate.LLVM.Native.Target
import Data.Array.Accelerate.LLVM.Native.CodeGen.Fold
import Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
import Data.Array.Accelerate.LLVM.Native.CodeGen.Map
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute
import Data.Array.Accelerate.LLVM.Native.CodeGen.Scan
import Data.Array.Accelerate.LLVM.Native.CodeGen.Stencil


instance Skeleton Native where
  map _         = mkMap
  generate _    = mkGenerate
  fold _        = mkFold
  fold1 _       = mkFold1
  permute _     = mkPermute
  scanl _       = mkScanl
  scanr _       = mkScanr
  scanl1 _      = mkScanl1
  scanr1 _      = mkScanr1
  scanl' _      = mkScanl'
  scanr' _      = mkScanr'
  foldSeg _     = mkFoldSeg
  fold1Seg _    = mkFold1Seg
  stencil _     = mkStencil
  stencil2 _    = mkStencil2

