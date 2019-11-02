module Landau where

import Data.List (foldl1')
import qualified Data.MemoCombinators as Memo

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

landau3 :: Integer -> Integer
landau3 = aux
  where
    aux n | n <= 0    = 0
          | otherwise = go 1 n

    m :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer
    m = Memo.memo2 Memo.integral Memo.integral
    
    go = m go'
    
    go' i n
      | i > n   = error "Never reach here?"
      | 2*i > n = n
      | otherwise = maximum $ n : [ lcm k (go k (n-k)) | k <- [i .. n `div` 2]]

