#!/usr/bin/env cabal
{- cabal:
build-depends: base, random, vector
-}
{-# LANGUAGE BangPatterns #-}
module Main(main) where

import Control.Monad

import qualified Data.Vector as V
import Data.List (unfoldr)

import System.Random

main :: IO ()
main =
  do g <- newStdGen
     V.ifoldM'_ f g collatzTable
  where
    threshold = 100
    f :: StdGen -> Int -> Int -> IO StdGen
    f g 0 _ = return g
    f g i n | i <= threshold =
      do putStrLn $ show i ++ "," ++ show n
         return g
    f g i n =
      do let (r, g') = randomR (0, i-1) g
         when (r <= 100) $
           putStrLn $ show i ++ "," ++ show n
         return g'

tableSize :: Int
tableSize = 10001

collatzTable :: V.Vector Int
collatzTable = V.generate tableSize collatz

step :: Int -> Int
step n | even n    = n `div` 2
       | otherwise = 3 * n + 1

collatz :: Int -> Int
collatz 0 = 0
collatz 1 = 1
collatz n = collatzAux 1 (step n)
  where
    collatzAux !count !n
      | n < tableSize = count + collatzTable V.! n
      | otherwise     = collatzAux (1 + count) (step n)

chunks :: Int -> V.Vector a -> [V.Vector a]
chunks n = unfoldr f
  where
    f xs | V.length xs == 0 = Nothing
         | otherwise        = Just (V.splitAt n xs)
