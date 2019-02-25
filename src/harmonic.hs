{-

Various ways to compute harmonic numbers and their accuracy

-}
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
    walk i !acc (Leaf x)
      | i == 1    = acc + x
      | otherwise = error "Never come here!"

data Tree = Node !Int    -- ^ Number of the leaves in the left child
                 !Double -- ^ Sum of the leaves in the left child
                 Tree    -- ^ the left child
                 Tree    -- ^ the right child
          | Leaf !Double

harmonicTreeMemo :: Tree
harmonicTreeMemo = go $ map (Leaf . recip . fromIntegral) [(1 :: Integer) ..]
  where
    go (t:ts) = t `plus` go (pairs ts)
    go [] = error "argument must be an infinite list"

    pairs (t:u:ts) = plus t u : pairs ts
    pairs _        = error "argument must be an infinite list"
    
    plus t1 t2 = let (n, x) = tsum t1
                 in Node n x t1 t2
    
    tsum (Leaf x) = (1, x)
    tsum (Node m x _ t2) =
      case tsum t2 of
        (n, y) -> (m+n, x+y)

{-

https://en.wikipedia.org/wiki/Harmonic_number#Calculation

-}
harmonicFormula :: Int -> Double
harmonicFormula n =
  let n' = fromIntegral n
  in log n' + eulerGamma + 1/(2*n') - 1/(12*n'*n') + 1/(120*n'*n'*n'*n')

eulerGamma :: Double
eulerGamma = 0.57721566490153286060

harmonicFinal :: Int -> Double
harmonicFinal n | n <= 1000 = harmonicTree n
                | otherwise = harmonicFormula n

deltaL, deltaT, deltaF, deltaFi :: Int -> Double
deltaL n = abs $ harmonicLinear n - harmonic n
deltaT n = abs $ harmonicTree n - harmonic n
deltaF n = abs $ harmonicFormula n - harmonic n
deltaFi n = abs $ harmonicFinal n - harmonic n

main :: IO ()
main = do
  forM_ [1..1000] $ \x ->
    putStrLn $ show x ++ "," ++ show (deltaL x)
                      ++ "," ++ show (deltaT x)
                      ++ "," ++ show (deltaF x)
                      ++ "," ++ show (deltaFi x)
  putStrLn "--------------------------"
  forM_ [1..100] $ \x ->
    do let n = 1000 * x
       putStrLn $ show n ++ "," ++ show (deltaL n)
                         ++ "," ++ show (deltaT n)
                         ++ "," ++ show (deltaF n)
                         ++ "," ++ show (deltaFi n)
