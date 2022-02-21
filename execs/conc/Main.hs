{-# LANGUAGE NumericUnderscores, BangPatterns #-}
module Main where

import Control.Concurrent
import Control.Parallel.Strategies
import System.IO.Unsafe

-- Checks Fermat's little theorem holds.
-- It should return 1 always.
task :: Int -> Int
task x = if fermat p x == x `mod` p then 1 else 0
  where p = 5003 -- is prime number

-- Fermat's little theorem:
--   If p is a prime number, x ^ p === x  (modulo p)
fermat :: Int -> Int -> Int
fermat p x = powModulo p x p

-- powModulo p x y = (x ^ y) `mod` p
powModulo :: Int -> Int -> Int -> Int
powModulo p x y = go y 1
  where
    go 0 !r = r
    go k !r = go (pred k) ((x * r) `mod` p)

-----------------------------------------------

runSeq :: (Int -> Int) -> [Int] -> IO ()
runSeq f xs = print $ sum (map f xs)

runSeq' :: MVar a -> (Int -> Int) -> [Int] -> IO ()
runSeq' sig f = loop 0
  where
    loop !acc [] = print acc
    loop !acc (x:xs) = do
      alive <- isEmptyMVar sig
      if alive
        then loop (acc + f x) xs
        else print acc

runParMap :: (Int -> Int) -> [Int] -> IO ()
runParMap f xs = print $ sum (parMap rseq f xs)

runParMapBuf :: (Int -> Int) -> [Int] -> IO ()
runParMapBuf f xs = print $ sum (map f xs `using` parBuffer bufSize rseq)

bufSize :: Int
bufSize = 32

runChunked' :: MVar a -> Strategy [Int] -> (Int -> Int) -> [Int] -> IO ()
runChunked' sig strat f = loop 0
  where
    chunkSize = 1000
    
    loop !acc [] = print acc
    loop !acc xs = do
      alive <- isEmptyMVar sig
      if alive
        then let (current, rest) = splitAt chunkSize xs
                 currentSum = sum (map f current `using` strat)
             in loop (acc + currentSum) rest
        else print acc

main :: IO ()
main = do
  -- Create a MVar which is filled 3 seconds later
  sig <- newEmptyMVar
  _ <- forkIO $ threadDelay 3_000_000 >> putMVar sig ()
  
  let -- Returns 0 when aborting.
      -- Note that task always returns 1.
      task' = unsafeCheckAbort sig 0 task
      xs = [1..1_000_000]
  -- runSeq task xs
  -- runSeq' sig task xs
  -- runSeq task' xs
  -- runParMap task' xs
  -- runParMapBuf task' xs
  -- runChunked' sig (parList rseq) task xs
  runChunked' sig (parBuffer bufSize rseq) task xs

-- This is EVIL utility function!
--
-- Modify a pure function `f :: a -> b` to make it return
-- a default value `b`, depending on whether the given `MVar`
-- is full on the time `f a` is evaluated.
-- 
-- Of course the returned function is not pure!
unsafeCheckAbort :: MVar x -> b -> (a -> b) -> (a -> b)
unsafeCheckAbort sig def f a = unsafePerformIO $
  do alive <- isEmptyMVar sig
     if alive
       then return (f a)
       else return def
