module Combinatorics where

import Data.Foldable (foldl')
import Control.Monad (guard)

import qualified Data.Vector.Unboxed as UV

-- |
--
-- > UV.length sumRows == numRows
-- > UV.length sumCols == numCols
-- > UV.length entries == numRows * numCols
data Table = MkTable {
    numRows :: Int,
    sumRows :: UV.Vector Int,
    numCols :: Int,
    sumCols :: UV.Vector Int,
    entries :: UV.Vector Int
    -- ^ row-major
  }
  deriving (Show)

instance Eq Table where
  x == y = numRows x == numRows y && entries x == entries y

-- | Enumerate partitions of @n@
--
-- - Unique up to reordering
-- - Descending order
partitions :: Int -> [[Int]]
partitions n0 = go n0 n0
  where
    go i n
      | n < 0   = []
      | n == 0  = [[]]
      | i <= 0  = []
      | i > n   = go n n
      | otherwise =
          [ i : rest | rest <- go i (n-i) ] ++
          go (i-1) n

-- | Enumerate partitions of @n@ of up to @k@ integers.
--   
-- * Unique up to reordering. e.g. [1,2,0] and [2,1,0] are considered equal
-- * A returned partition is represented as a list of positive integers in descending order,
--   padded to length @k@ with @0@.
partitionsK :: Int -> Int -> [[Int]]
partitionsK n0 k0 = go k0 n0 n0
  where
    go k i n
      | n < 0   = []
      | n == 0  = [ replicate k 0 ]
      | i <= 0  = []
      | i > n   = go k n n
      | otherwise =
          [ i : rest | rest <- go (k-1) i (n-i) ] ++
          go k (i-1) n

-- | @distributions n k@ enumerates distributions of @n@ totals to @k@ integers
--   
-- * The resulted numbers are ordered. e.g. [1,2,0] and [2,1,0] are
--   considered distinct distributions
distributions :: Int -> Int -> [[Int]]
distributions n k
  | n < 0 || k < 0 = []
  | n == 0         = [ replicate k 0 ]
  | k == 1         = [[n]]
  | otherwise      = do
      x <- [0 .. n]
      xs <- distributions (n-x) (k-1)
      pure (x:xs)


contigencyTables :: UV.Vector Int -> UV.Vector Int -> [Table]
contigencyTables rows cols = _ -- TODO

split :: Int -> [(Int, Int)]
split n = [ (i, n-i) | i <- [0..n] ]

split3 :: Int -> [(Int, Int, Int)]
split3 n = [ (i, j, k) | (i,jk) <- split n, (j,k) <- split jk ]
