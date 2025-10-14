module Math.CountCoSemigroup
  ( partitionsCount,
    twoPartialFunctionsCount,
    weaktransCosemigroupsCount,
    cosemigroupsCount
  )
where

import Data.List (group)
import qualified Data.MemoCombinators as Memo
import Math.Combinatorics (partitions, binomial)
import Math.ContingencyTable (uniquePointedContingencyTables)

-- | @partitionsCount n k@ = number of unique partitions of n into k positive integers
--
--  @partitionsCount (n + k) k@ =  number of unique partitions of n into **up to** k **non-negative** integers
partitionsCount :: Int -> Int -> Int
partitionsCount = Memo.memo2 Memo.integral Memo.integral go
  where
    go n k | n < 0 || k < 0 = 0
    go 0 0 = 1
    go _ 0 = 0
    go n k = partitionsCount (n - 1) (k - 1) + partitionsCount (n - k) k

parts :: Int -> [(Int, Int)]
parts m = [(k, m - k) | k <- [0 .. m]]

-- count # of functions (a -> (Maybe b, Maybe c)) up to iso of a, b, and c
twoPartialFunctionsCount :: Int -> Int -> Int -> Int
twoPartialFunctionsCount = Memo.memo3 Memo.integral Memo.integral Memo.integral go
  where
    go a b c = length $ uniquePointedContingencyTables b c a

-- split of n is ordered triple (c,l,r) such that
--  c + l + r + 1 == n
-- (c,l,r are nonnegative integers)
splits :: Int -> [(Int, Int, Int)]
splits n
  | n <= 0 = []
  | otherwise = do
      let n' = n - 1
      (c, lr) <- parts n'
      (l, r) <- parts lr
      pure (c, l, r)

-- count # of "weakly transitive" Cosemigroups
weaktransCosemigroupsCount :: Int -> Int
weaktransCosemigroupsCount = Memo.integral splitCount'
  where
    splitCount' n = sum [twoPartialFunctionsCount c l r | (c, l, r) <- splits n]

-- count # of CoSemigroups
cosemigroupsCount :: Int -> Int
cosemigroupsCount n = sum [countForPartition as | as <- partitions n]
  where
    countForPartition = product . map countByGroup . group
    countByGroup [] = error "group is alway nonempty"
    countByGroup (a : rest) = binomial' (weaktransCosemigroupsCount a + k - 1) k
      where
        k = 1 + length rest

binomial' :: Int -> Int -> Int
binomial' n k = fromInteger (binomial (toInteger n) (toInteger k))
