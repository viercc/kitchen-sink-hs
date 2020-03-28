#!/usr/bin/env cabal
{- cabal:
build-depends: base
ghc-options:   -threaded
-}
module Main where

import Control.Monad

import System.Timeout
import Control.Concurrent

main :: IO ()
main = do
  counter <- newMVar (0 :: Int)
  _ <- timeout 1000000 $ forever $ do
    c <- readMVar counter
    threadDelay 1000
    swapMVar counter $! (c + 1)
  print =<< tryTakeMVar counter
