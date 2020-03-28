#!/usr/bin/env cabal
{- cabal:
build-depends: base, integer-logarithms, arithmoi, data-memocombinators
ghc-options:   -O2
-}
{-# LANGUAGE BangPatterns #-}
module Main(main) where

import Control.Applicative ((<|>))
import qualified Math.NumberTheory.Primes as Prime
import Math.NumberTheory.Logarithms
import qualified Data.MemoCombinators as Memo

costHi :: Integer -> Int
costHi = loop 0
  where loop !acc 0 = acc - 2
        loop !acc n = case quotRem n 2 of
          (q, r) -> loop (acc + 2 + fromInteger r) q

costLo :: Integer -> Int
costLo n | n <= 5    = fromInteger n
         | otherwise = max 5 (3 * integerLogBase 3 n)

data Expr = Leaf !Int | Plus !Expr !Expr | Times !Expr !Expr
  deriving (Eq, Ord)

instance Num Expr where
  fromInteger = Leaf . fromInteger
  (+) = Plus
  (*) = Times

instance Show Expr where
  showsPrec p (Leaf n) = showsPrec p n
  showsPrec p (Plus x y) = showParen (6 < p) $ showsPrec 7 x . (" + " ++) . showsPrec 6 y
  showsPrec p (Times x y) = showParen (7 < p) $ showsPrec 8 x . (" * " ++) . showsPrec 7 y

minimalExpr :: Integer -> (Expr, Int)
minimalExpr n = case solve (costHi n) n of
  Nothing -> error $ "should never happen! " ++ show n
  Just ec -> ec

solve :: Int -> Integer -> Maybe (Expr, Int)
solve = Memo.integral solveC

solveC :: Int -> Integer -> Maybe (Expr, Int)
solveC cmax | cmax <= 5 =
  \n -> let n' = fromInteger n
        in if n' <= cmax then Just (Leaf n', n') else Nothing
solveC cmax = Memo.integral solve'
  where
    prev = solve (cmax - 1)
    solve' n = case prev n of
      ans@(Just _) -> ans
      Nothing      -> solveTimes n cmax <|> solvePlus n cmax

solvePlus :: Integer -> Int -> Maybe (Expr, Int)
solvePlus n cmax = foldr (<|>) Nothing $
  do (j,k) <- splitPlus n cmax
     Just (jExpr, cj) <- [solve cmax j]
     Just (kExpr, ck)  <- [solve (cmax - cj) k]
     return $ Just (Plus jExpr kExpr, cj + ck)

splitPlus :: Integer -> Int -> [(Integer, Integer)]
splitPlus n cmax
  | n <= 5 = []
  | otherwise =
      takeWhile cond [(j, n-j) | j <- [1 .. n `div` 2] ]
  where
    cond (j,k) = costLo j + costLo k < cmax

solveTimes :: Integer -> Int -> Maybe (Expr, Int)
solveTimes n cmax = foldr (<|>) Nothing $
  do (j,k) <- splitTimes n
     Just (jExpr, cj) <- [solve cmax j]
     Just (kExpr, ck) <- [solve (cmax - cj) k]
     return $ Just (Times jExpr kExpr, cj + ck)

splitTimes :: Integer -> [(Integer, Integer)]
splitTimes = Memo.integral splitTimes'
  where
    splitTimes' n | n <= 5 = []
    splitTimes' n =
      [ (j, k) | j <- takeWhile (\i -> i*i <= n) primes
               , let (k, r) = quotRem n j
               , r == 0 ]

primes :: [Integer]
primes = Prime.unPrime <$> Prime.primes

main :: IO ()
main = mapM_ (print . minimalExpr . (2^)) [35 .. 45::Int]
