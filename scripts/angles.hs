#!/usr/bin/env cabal
{- cabal:
build-depends: base, vector
-}
module Main where

import Data.Foldable (foldl')
import Control.Monad (guard)

import qualified Data.Vector.Unboxed as V

type Table = [V.Vector Int]
type Marginal = V.Vector Int

partition :: Int -> Int -> [[Int]]
partition n len = partitionWithCap n (replicate len n)

partitionWithCap :: Int -> [Int] -> [[Int]]
partitionWithCap n [] = [ [] | n == 0]
partitionWithCap n [k] = [ [n] | n <= k ]
partitionWithCap n (k:ks) =
  do x <- [0 .. min n k]
     xs <- partitionWithCap (n-x) ks
     pure (x:xs)

searchOnMarginal :: Marginal -> [Table]
searchOnMarginal qs = go (zip [1..] (V.toList qs)) qs qs
    where
      len = V.length qs
      isEmpty = V.all (== 0)
      go [] bs cs = [ [] | isEmpty bs && isEmpty cs ]
      go ((i,a):as) bs cs =
        do row <- V.fromList <$> partitionWithCap a (V.toList bs)
           let bs' = V.zipWith (-) bs row
           cs' <- subCs i row cs
           rest <- go as bs' cs'
           pure (row : rest)
      
      subCs i row cs = [ cs' | V.all (>= 0) cs' ]
        where
          cs' = V.imap subCell cs
          subCell k c =
            let j = 2 * len - i - k
                r | 1 <= j && j <= len = row V.! (j-1)
                  | otherwise          = 0
            in c - r

isReduced :: Table -> Bool
isReduced = (== 1) . foldl' gcd 0 . map (V.foldl' gcd 0)

search :: Int -> [Table]
search size =
  do total <- [1..]
     qs <- partition total size
     table <- searchOnMarginal (V.fromList qs)
     guard (isReduced table)
     pure table

printTable :: Table -> IO ()
printTable table = do
    putStrLn header
    mapM_ printRow table
    putStrLn ""
  where
    sumTable = sum $ map V.sum table
    header = "# n=" ++ show sumTable
    printRow = putStrLn . unwords . map show . V.toList

main :: IO ()
main = mapM_ printTable (take 200 $ search 4)
