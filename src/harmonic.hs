{-# LANGUAGE BangPatterns #-}
module Main where

import qualified Data.MemoCombinators as Memo
import Data.Decimal
import Control.Monad (forM_)

----------------------------

accurateHarmonic :: Int -> Decimal
accurateHarmonic = Memo.integral f
  where
    f n
      | n <= 0 = 0
      | otherwise = accurateHarmonic (n-1) + recip (fromIntegral n)

harmonic :: Int -> Double
harmonic = fromRational . toRational . accurateHarmonic

harmonicLinear :: Int -> Double
harmonicLinear = Memo.integral f
  where
    f n
      | n <= 0 = 0
      | otherwise = harmonicLinear (n-1) + recip (fromIntegral n)

harmonicTree :: Int -> Double
harmonicTree n = walk n 0 harmonicTreeMemo
  where
    walk 0 !acc _ = acc
    walk i !acc (Node m x t1 t2)
      | i >= m    = walk (i-m) (acc+x) t2
      | otherwise = walk i acc t1
    walk _ _ Nil = error "Never come here"

data Tree = Node !Int !Double Tree Tree
          | Nil

harmonicTreeMemo :: Tree
harmonicTreeMemo = go $ map (leaf . recip . fromIntegral) [(1 :: Integer) ..]
  where
    leaf x = Node 1 x Nil Nil
    
    go [] = Nil
    go (t:ts) = t `plus` go (pairs ts)

    pairs (t:u:ts) = plus t u : pairs ts
    pairs ts       = ts
    
    plus t1 t2 = let (n, x) = tsum t1
                 in Node n x t1 t2
    
    tsum Nil = (0, 0)
    tsum (Node m x _ t2) =
      case tsum t2 of
        (n, y) -> (m+n, x+y)

deltaL, deltaT :: Int -> Double
deltaL n = harmonicLinear n - harmonic n
deltaT n = harmonicTree n - harmonic n

main :: IO ()
main =
  forM_ [1..1000] $ \x ->
    do let n = 1000 * x
       putStrLn $ show n ++ "," ++ show (deltaL n) ++ "," ++ show (deltaT n)
