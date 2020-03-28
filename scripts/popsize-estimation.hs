#!/usr/bin/env cabal
{- cabal:
build-depends: base, containers
-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
module Main where

import Data.Foldable (for_)
import qualified Data.Map as Map

main :: IO ()
main = do
  let n = 10
      k = 7
  putStrLn $ "(n,k)=" ++ show (n,k)
  for_ [0..10] $ \a0 ->
    putStrLn $ "relativeLik n k " ++ show a0 ++ " = " ++ show (relativeLik n k a0)

factorial :: Integer -> Integer
factorial = go 1
  where
    go !acc !n
      | n < 0     = 0
      | n == 0    = acc
      | n == 1    = acc
      | otherwise = go (n * acc) (n - 1)

minusInf :: Double
minusInf = -1/0

-- logFac = log . factorial
logFac :: Integer -> Double
logFac = go 0
  where
    go !acc !n
      | n < 0     = minusInf
      | n == 0    = acc
      | n == 1    = acc
      | otherwise = go (ilog n + acc) (n - 1)

    ilog = log . fromInteger

-- logComb n k = log . combinations n k
logComb n k
  | n < 0 = minusInf
  | k < 0 = minusInf
  | n < k = minusInf
  | k > n - k = go n (n - k) 0
  | otherwise = go n k 0
  where
    go _ 0 !acc = acc
    go m i !acc = go (m - 1) (i - 1) (ilog m - ilog i + acc)
    ilog = log . fromInteger

logCount :: [Integer] -> Double
logCount as =
  let sampSize = sum $ zipWith (*) [0..] as
      popSize = sum as
  in logFac sampSize
      - sum [ fromInteger a * logFac i | (i,a) <- zip [0..] as ]
      + logFac popSize
      - sum [ logFac a | a <- as ]

logLik :: [Integer] ->  Double
logLik as =
  let sampSize = sum $ zipWith (*) [0..] as
      popSize = sum as
  in logCount as - fromInteger sampSize * log (fromInteger popSize)

relativeLik :: Integer -> Integer -> Integer -> Double
relativeLik n k a0 =
  let m = k + a0
      e = fromInteger n * log (fromInteger m / fromInteger k)
  in logComb m k - e

newtype X = X Integer
  deriving (Show, Eq, Ord)

allCombs :: Integer -> Integer -> [[X]]
allCombs n = go
  where
    xs = X <$> [1 .. n]
    go k | k <= 0    = [[]]
         | otherwise = (:) <$> xs <*> go (k - 1)

freqs :: (Ord a, Num b) => [a] -> [b]
freqs = Map.elems . Map.fromListWith (+) . map (,1)

freqs2freqSeq :: [Integer] -> [Integer]
freqs2freqSeq = foldr plus [] . map u
  where
    plus [] ys = ys
    plus xs [] = xs
    plus (x:xs) (y:ys) = (x+y) : plus xs ys

    u 1 = [1]
    u n = 0 : u (n-1)

makeTab :: Integer -> Integer -> Map.Map [Integer] Integer
makeTab n k =
  let dat = allCombs n k
      conv fs =
        n - toInteger (length fs) : freqs2freqSeq fs
      freqdat = conv . freqs <$> dat
  in Map.fromListWith (+) . map (,1) $ freqdat
