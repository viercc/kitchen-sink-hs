{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Math.Combinatorics(
  catalan, binomial,

  partitions, partitionsK,

  Bag, IntBag,
  bags,
  bagsSet,
  bagsIntSet,

  subIntBags,
  subBags,
) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.MultiSet qualified as Bag
import Data.IntMultiSet qualified as IntBag
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.MemoCombinators qualified as Memo

-- * Basic functions

-- | カタラン数
catalan :: Integer -> Integer
catalan = Memo.integral c
  where
    c n
      | n < 0 = 0
      | n == 0 = 1
      | otherwise = (2 * (2 * n - 1) * catalan (n - 1)) `div` (n + 1)

-- | 二項係数
binomial :: Integer -> Integer -> Integer
binomial = Memo.memo2 Memo.integral Memo.integral binom
  where
    binom n k
      | n < 0 || k < 0 || k > n = 0
      | 2 * k > n = loop n (n - k)
      | otherwise = loop n k
    
    -- 0 <= k <= 2 * k <= n
    loop _ 0 = 1
    loop n k = (loop (n - 1) (k - 1) * n) `div` k

-- * Partitions

-- | Enumerate partitions of @n@ to positive integers
--
-- - The returned partitions are unique up to reordering.
-- - Each of the returned partition is in descending order.
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

-- | Enumerate partitions of @n@ to @k@ nonnegative integers (0 included)
--
-- - The returned partitions are unique up to reordering.
-- - Each of the returned partition is in descending order.
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

-- * Distributions

type Bag = Bag.MultiSet
type IntBag = IntBag.IntMultiSet

-- | @bags n k@ enumerates bags (multisets) of @n@ totals to
--   @k@ kind of items, each represented by integers @[0 .. k - 1]@.
--
-- @
-- bags n k == bagsIntSet n (IntSet.fromList [0 .. k - 1])
-- @
bags :: Int -> Int -> [IntBag]
bags n k
  | n < 0 || k < 0 = []
  | n == 0 = [IntBag.empty]
  | k == 0 = [] {- (n > 0) assumed -}
  | k == 1 = [IntBag.insertMany 0 n IntBag.empty]
  | otherwise = do
      x <- [0 .. n]
      xs <- bags (n - x) (k - 1)
      pure (IntBag.insertMany (k - 1) x xs)

bagsSet :: (Ord k) => Int -> Set k -> [Bag k]
bagsSet total keySet = loop total (Set.toDescList keySet)
  where
    loop n ks
      | n < 0 = []
      | n == 0 = [Bag.empty]
      | otherwise {- (n > 0) assumed -} = case ks of
          [] -> []
          [k] -> [Bag.insertMany k n Bag.empty]
          (k:ks') -> do
            x <- [0 .. n]
            xs <- loop (n - x) ks'
            pure (Bag.insertMany k x xs)

-- | @bagsIntSet total keySet@ enumerates bags of
--   items in a set @keySet@, with total number @total@.
bagsIntSet :: Int -> IntSet -> [IntBag]
bagsIntSet total keySet = loop total (IntSet.toDescList keySet)
  where
    loop n ks
      | n < 0 = []
      | n == 0 = [IntBag.empty]
      | otherwise {- (n > 0) assumed -} = case ks of
          [] -> []
          [k] -> [IntBag.insertMany k n IntBag.empty]
          (k:ks') -> do
            x <- [0 .. n]
            xs <- loop (n - x) ks'
            pure (IntBag.insertMany k x xs)

-- | @subIntBags n as@ enumerates bags @bs@ of @n@ totals to @k = length as@ integers,
--   under the restriction @'IntBag.isSubsetOf' bs as@.
-- 
--   The returned is a list of pair @(bs, cs)@ where @bs@ is the distribution of total @n@,
--   and @cs@ is the difference @as 'IntBag.\\' bs@
subIntBags :: Int -> IntBag -> [(IntBag, IntBag)]
subIntBags n as = go n (IntBag.size as) (IntBag.toOccurList as)
  where
    go m _ [] = [(IntBag.empty, IntBag.empty) | m == 0]
    go m t ((key, a) : rest)
      | m > t = []
      | otherwise = do 
          -- (k <= a) && (m - k) <= (t - a)
          -- m + a - t <= k
          let minK = max 0 (m + a - t)
          k <- [minK .. a]
          (bs, cs) <- go (m - k) (t - a) rest
          pure $ (IntBag.insertMany key k bs, IntBag.insertMany key (a - k) cs)

-- | @subBags n as@ enumerates bags @bs@ of @n@ totals to @k = length as@ integers,
--   under the restriction @'Bag.isSubsetOf' bs as@.
-- 
--   The returned is a list of pair @(bs, cs)@ where @bs@ is the distribution of total @n@,
--   and @cs@ is the difference @as 'Bag.\\' bs@
subBags :: (Ord k) => Int -> Bag k -> [(Bag k, Bag k)]
subBags n as = go n (Bag.size as) (Bag.toOccurList as)
  where
    go m _ [] = [(Bag.empty, Bag.empty) | m == 0]
    go m t ((key, a) : rest)
      | m > t = []
      | otherwise = do 
          -- (k <= a) && (m - k) <= (t - a)
          -- m + a - t <= k
          let minK = max 0 (m + a - t)
          k <- [minK .. a]
          (bs, cs) <- go (m - k) (t - a) rest
          pure $ (Bag.insertMany key k bs, Bag.insertMany key (a - k) cs)
