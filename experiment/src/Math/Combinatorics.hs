{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Math.Combinatorics where

-- | Enumerate partitions of @n@
--
-- - Unique up to reordering
-- - Descending order
partitions :: Int -> [[Int]]
partitions n0 = go n0 n0
  where
    go i n
      | n < 0 = []
      | n == 0 = [[]]
      | i <= 0 = []
      | i > n = go n n
      | otherwise =
          [i : rest | rest <- go i (n - i)]
            ++ go (i - 1) n

-- | Enumerate partitions of @n@ by @k@ natural numbers.
--
-- * Unique up to reordering. e.g. [1,2,3] and [2,1,3] are considered equal
-- * A returned partition is represented as a list of nonnegative integers in descending order
partitionsK :: Int -> Int -> [[Int]]
partitionsK n0 k0 = go k0 n0 n0
  where
    go k n m
      | k < 0 = []
      | n < m = go k n n
      | k * m < n = []
      | n == 0 = [replicate k 0]
      | k == 1 = [[n]]
      | otherwise = [m : xs | xs <- go (k - 1) (n - m) m] ++ go k n (m - 1)

-- | @distributions n k@ enumerates distributions of @n@ totals to @k@ integers
--
-- * The resulted numbers are ordered. e.g. [1,2,0] and [2,1,0] are
--   considered distinct distributions
distributions :: Int -> Int -> [[Int]]
distributions n k
  | n < 0 || k < 0 = []
  | n == 0 = [replicate k 0]
  | k == 1 = [[n]]
  | otherwise = do
      x <- [0 .. n]
      xs <- distributions (n - x) (k - 1)
      pure (x : xs)

-- | @subDistributions n as@ enumerates distributions @bs@ of @n@ totals to @k = length as@ integers,
--   under the restriction @bs !! i <= as !! i@ for all @i `elem` [0 .. k-1]@.
subDistributions :: Int -> [Int] -> [([Int], [Int])]
subDistributions n as = go n (sum as) as
  where
    go m _ [] = [([], []) | m == 0]
    go m t (a : as')
      | m > t = []
      | otherwise =
          -- (k <= a) && (m - k) <= (t - a)
          -- m + a - t <= k
          let minK = max 0 (m + a - t)
           in [(k : ks, (a - k) : rs) | k <- [minK .. a], (ks, rs) <- go (m - k) (t - a) as']
