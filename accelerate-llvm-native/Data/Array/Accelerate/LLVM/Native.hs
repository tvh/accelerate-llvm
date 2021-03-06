{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP          #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements a backend for the /Accelerate/ language targeting
-- multicore CPUs. Expressions are on-line translated into LLVM code, which is
-- just-in-time executed in parallel over the available CPUs. Functions are
-- automatically parallel, provided you specify '+RTS -Nwhatever' on the command
-- line when running the program.
--

module Data.Array.Accelerate.LLVM.Native (

  Arrays,

  -- ** Parallel execution
  run, run1, stream,

) where

-- accelerate
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Smart                      ( Acc )
import Data.Array.Accelerate.Array.Sugar                ( Arrays )

import Data.Array.Accelerate.LLVM.Native.Compile
import Data.Array.Accelerate.LLVM.Native.Execute
import Data.Array.Accelerate.LLVM.Native.State

#if ACCELERATE_DEBUG
import Data.Array.Accelerate.Debug
#endif

-- standard library
import Control.Monad.Trans
import System.IO.Unsafe
import GHC.Conc                                         ( numCapabilities )


-- Accelerate: LLVM backend for multicore CPUs
-- -------------------------------------------

-- | Compile and run a complete embedded array program.
--
-- Note that it is recommended that you use 'run1' whenever possible.
--
run :: Arrays a => Acc a -> a
run a = unsafePerformIO execute
  where
    !acc        = convertAccWith config a
    execute     = evalNative defaultTarget (compileAcc acc >>= dumpStats >>= executeAcc)


-- | Prepare and execute an embedded array program of one argument.
--
-- This function can be used to improve performance in cases where the array
-- program is constant between invocations, because it enables us to bypass
-- front-end conversion stages and move directly to the execution phase. If you
-- have a computation applied repeatedly to different input data, use this,
-- specifying any changing aspects of the computation via the input parameter.
-- If the function is only evaluated once, this is equivalent to 'run'.
--
-- To use 'run1' effectively you must express your program as a function of one
-- argument. If your program takes more than one argument, you can use
-- 'Data.Array.Accelerate.lift' and 'Data.Array.Accelerate.unlift' to tuple up
-- the arguments.
--
-- At an example, once your program is expressed as a function of one argument,
-- instead of the usual:
--
-- > step :: Acc (Vector a) -> Acc (Vector b)
-- > step = ...
-- >
-- > simulate :: Vector a -> Vector b
-- > simulate xs = run $ step (use xs)
--
-- Instead write:
--
-- > simulate xs = run1 step xs
--
-- You can use the debugging options to check whether this is working
-- successfully by, for example, observing no output from the @-ddump-cc@ flag
-- at the second and subsequent invocations.
--
-- See the programs in the 'accelerate-examples' package for examples.
--
run1 :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> b
run1 f = \a -> unsafePerformIO (execute a)
  where
    !acc        = convertAfunWith config f
    !afun       = unsafePerformIO $ evalNative defaultTarget (compileAfun acc) >>= dumpStats
    execute a   = evalNative defaultTarget (executeAfun1 afun a)


-- | Stream a lazily read list of input arrays through the given program,
-- collecting results as we go.
--
stream :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> [a] -> [b]
stream f arrs = map go arrs
  where
    !go = run1 f


-- How the Accelerate program should be evaluated.
--
-- TODO: make sharing/fusion runtime configurable via debug flags or otherwise.
--
config :: Phase
config =  Phase
  { recoverAccSharing      = True
  , recoverExpSharing      = True
  , floatOutAccFromExp     = True
  , enableAccFusion        = True
  , convertOffsetOfSegment = True
  }


dumpStats :: MonadIO m => a -> m a
#if ACCELERATE_DEBUG
dumpStats next = do
  stats <- liftIO simplCount
  liftIO $ traceMessage dump_simpl_stats (show stats)
  liftIO $ resetSimplCount
  return next
#else
dumpStats next = return next
#endif

