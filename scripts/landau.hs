#!/usr/bin/env cabal
{- cabal:
build-depends: base, data-memocombinators, gauge
ghc-options:   -O2
-}
module Main(main) where

import Data.List (foldl1')
import qualified Data.MemoCombinators as Memo
import Gauge.Main

main :: IO ()
main =
  do print (($ 10) <$> methods)
     defaultMain
       [ bgroup ("n="++show n)
           [ bench ("landau" ++ show k) (whnf method n)
             | (k, method) <- zip [1..] methods ]
         | n <- [10, 20, 40]
       ]
  where
    methods = [landau1, landau2, landau3]

partitions :: Integer -> [[Integer]]
partitions = go 1
  where
    go i n
      | i > n = []
      | otherwise = [n] : [ k : ps | k <- [i .. n `div` 2]
                                   , ps <- go k (n-k) ]

landau1 :: Integer -> Integer
landau1 n
  | n <= 0    = 0
  | otherwise = maximum $ fmap (foldl1' lcm) $ partitions n

landau2 :: Integer -> Integer
landau2 = aux
  where
    aux n | n <= 0    = 0
          | otherwise = go 1 n
    
    go i n
      | i > n   = error "Never reach here?"
      | 2*i > n = n
      | otherwise = maximum $ n : [ lcm k (go k (n-k)) | k <- [i .. n `div` 2]]

memoII :: (Integer -> Integer -> a) -> Integer -> Integer -> a
memoII = Memo.memo2 Memo.integral Memo.integral

landau3 :: Integer -> Integer
landau3 = aux
  where
    aux n | n <= 0    = 0
          | otherwise = go 1 n
      where
        go = memoII go'
        go' i n
          | i > n   = error "Never reach here?"
          | 2*i > n = n
          | otherwise = maximum $ n : [ lcm k (go k (n-k)) | k <- [i .. n `div` 2]]
    
    

