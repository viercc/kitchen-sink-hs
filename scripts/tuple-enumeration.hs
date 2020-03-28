#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
module Main where

split :: Int -> [[Int]]
split n | n < 0 = []
        | otherwise = [[a,n-a]|a<-[0..n]]

tuples2 :: [[Int]]
tuples2 = [0..] >>= split

tuples4 :: [[Int]]
tuples4 = tuples2 >>= \ps -> concat <$> traverse split ps

tuples8 :: [[Int]]
tuples8 = tuples4 >>= \ps -> concat <$> traverse split ps

tuples16 :: [[Int]]
tuples16 = tuples8 >>= \ps -> concat <$> traverse split ps

main :: IO ()
main = mapM_ print $ take 20 tuples16
