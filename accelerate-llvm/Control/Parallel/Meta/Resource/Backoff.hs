{-# LANGUAGE RecordWildCards #-}
-- |
-- Module      : Control.Parallel.Meta.Resource.Backoff
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements exponential backoff so as to prevent spamming of
-- stealing actions. Most scheduler compositions should include this at the
-- bottom of the stack.
--
-- Inspired by the meta-par package. This package has a BSD license.
-- <http://hackage.haskell.org/package/meta-par>
--

module Control.Parallel.Meta.Resource.Backoff (

  mkResource,
  defaultWorkSearch, mkWorkSearch,

) where

import Data.IORef
import Data.Monoid

import Control.Concurrent
import Text.Printf

import Control.Parallel.Meta
import Control.Parallel.Meta.Worker
import qualified Data.Array.Accelerate.LLVM.Debug       as Debug


mkResource :: Resource
mkResource = Resource mempty defaultWorkSearch

defaultWorkSearch :: WorkSearch
defaultWorkSearch = mkWorkSearch 100 10000


-- | To construct the work search, we need to know the minimum and maximum
-- amount of time, in nanoseconds, to sleep. The exponential backoff policy is
-- always the same: it starts at 1µs and doubles at every failure.
--
-- The thing that changes over time is whether sleeping actually occurs. For
-- example, the 'defaultWorkSearch':
--
-- > mkWorkSearch 100 10000
--
-- will not sleep for the first 7 invocations (until 128), and then will sleep
-- an amount that doubles each time until it surpasses the maximum, at which
-- point it will always sleep for the maximum time (10ms)
--
mkWorkSearch :: Int -> Int -> WorkSearch
mkWorkSearch _        0       = WorkSearch $ \_ -> return Nothing
mkWorkSearch shortest longest = WorkSearch backoff
  where
    backoff Worker{..} = do
      failed   <- readIORef consecutiveFailures
      let sleep = min longest (2 ^ failed)
      if sleep >= shortest
         then do
           message workerId (printf "sleeping for %d µs" sleep)
           threadDelay sleep

         else do
           message workerId "not sleeping"
           return ()

      return Nothing


-- Debugging
-- ---------

{-# INLINE message #-}
message :: Int -> String -> IO ()
message tid msg = Debug.message Debug.dump_sched (printf "sched/backoff: [%d] %s" tid msg)

