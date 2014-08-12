{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Compile
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Compile (

  module Data.Array.Accelerate.LLVM.Compile,
  module Data.Array.Accelerate.LLVM.Native.Compile.Function,
  ExecutableR(..),

) where

-- llvm-general
import LLVM.General.AST                                         hiding ( Module )
import LLVM.General.Module                                      as LLVM
import LLVM.General.Context
import LLVM.General.Target
import LLVM.General.ExecutionEngine
import LLVM.General.Threading

-- accelerate
import Data.Array.Accelerate.Error                              ( internalError )
import Data.Array.Accelerate.Trafo                              ( DelayedOpenAcc )

import Data.Array.Accelerate.LLVM.CodeGen
import Data.Array.Accelerate.LLVM.Compile
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Environment           ( Gamma )
import Data.Array.Accelerate.LLVM.CodeGen.Module                ( Module(..) )

import Data.Array.Accelerate.LLVM.Native.Compile.Function
import Data.Array.Accelerate.LLVM.Native.Compile.Link
import Data.Array.Accelerate.LLVM.Native.Compile.Optimise

import Data.Array.Accelerate.LLVM.Native.Target
import Data.Array.Accelerate.LLVM.Native.CodeGen                ( )
import qualified Data.Array.Accelerate.LLVM.Native.Debug        as Debug

-- standard library
import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.State
import Data.Maybe

#if !MIN_VERSION_llvm_general(3,3,0)
import LLVM.General.Context
import Data.Word
import System.Directory
import System.IO
#endif


instance Compile Native where
  data ExecutableR Native = NativeR { executableR :: Function }
  compileForTarget        = compileForNativeTarget

instance Intrinsic Native


-- Compile an Accelerate expression for the native CPU target.
--
compileForNativeTarget :: DelayedOpenAcc aenv a -> Gamma aenv -> LLVM Native (ExecutableR Native)
compileForNativeTarget acc aenv = do
  liftIO $ setMultithreaded True

  target <- gets llvmTarget

  -- Generate code for this Acc operation
  let Module ast = llvmOfAcc target acc aenv
      triple     = fromMaybe "" (moduleTargetTriple ast)
      datalayout = moduleDataLayout ast

  -- Lower the generated LLVM AST all the way to JIT compiled functions.
  --
  -- See note: [Executing JIT-compiled functions]
  --
  -- Don't use the existing context stored in the LLVM state, as that would
  -- sometimes lead to a segfault. Instead, the worker thread runs in a new
  -- 'withContext'.
  --
  fun <- liftIO . startFunction $ do
    ctx     <- ContT withContext
    mdl     <- runErrorCont $ withModuleFromAST ctx ast
    machine <- runErrorCont withNativeTargetMachine
    libinfo <- ContT $ withTargetLibraryInfo triple

    liftIO $ optimiseModule datalayout (Just machine) (Just libinfo) mdl

    liftIO $ Debug.when Debug.verbose $ do
      Debug.message Debug.dump_llvm =<< moduleLLVMAssembly mdl
      Debug.message Debug.dump_asm  =<< runError (moduleTargetAssembly machine mdl)

    mcjit <- ContT $ withMCJIT ctx opt model ptrelim fast
    exe   <- ContT $ withModuleInEngine mcjit mdl
    liftIO $ getGlobalFunctions ast exe

  return $! NativeR fun
  where
    runErrorCont :: ((a -> IO r) -> ExceptT String IO r) -> ContT r IO a
    runErrorCont c = ContT $ \f -> runError $ c f

    runError    = either ($internalError "compileForNativeTarget") return <=< runExceptT

    opt         = Just 3        -- optimisation level
    model       = Nothing       -- code model?
    ptrelim     = Nothing       -- True to disable frame pointer elimination
    fast        = Just True     -- True to enable fast instruction selection



-- Shims to support llvm-general-3.2.*
-- -----------------------------------

#if !MIN_VERSION_llvm_general(3,3,0)
-- Generate LLVM assembly from a module
moduleLLVMAssembly :: LLVM.Module -> IO String
moduleLLVMAssembly = moduleString

-- Generate target specific assembly instructions
--
-- TODO: should really clean up the temporary file, but the contents are read
--       lazily, so...
--
moduleTargetAssembly :: TargetMachine -> LLVM.Module -> ErrorT String IO String
moduleTargetAssembly machine mdl = ErrorT $ do
  tmp    <- getTemporaryDirectory
  (fp,h) <- openTempFile tmp "accelerate-llvm.asm"
  ok     <- runErrorT $ LLVM.writeAssemblyToFile machine fp mdl
  case ok of
    Left e   -> return (Left e)
    Right () -> Right `fmap` hGetContents h

-- Bracket creation and destruction of a JIT compiler
--
type MCJIT = JIT

withMCJIT
    :: Context
    -> Maybe Word
    -> model
    -> fpe
    -> fis
    -> (MCJIT -> IO a)
    -> IO a
withMCJIT ctx opt _ _ _ action =
  withJIT ctx (fromMaybe 0 opt) action
#endif

