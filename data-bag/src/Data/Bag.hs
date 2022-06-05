{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
-- | Bag or \'multiset\' data structure.
module Data.Bag(
  Bag(),
  -- * Basic queries
  null, size, uniqueLength, count, isSubsetOf, isProperSubsetOf,

  -- * Construction
  empty, singleton,
  
  -- * Single-item operation
  insert, delete, pullOut,

  -- * Combine two bags
  append, union, intersection, difference, cartesianProduct,

  -- * Conversion
  fromFreqs,
  toFreqs, toAscFreqs, toDescFreqs,
  
  fromFreqsMap, toFreqsMap,

  fromList,
  fromAscList, fromDescList,
  fromDistinctAscList, fromDistinctDescList,
  toList, toAscList, toDescList,
) where

import Prelude hiding (null)

import qualified Data.Map.Strict as Map

import qualified Data.Foldable as F
import Control.Monad ((<=<))

import Data.Bag.Internal

-- * Queries

-- | O(1)
uniqueLength :: Bag k -> Int
uniqueLength (MkBag m) = Map.size m

-- | Number of an item in a bag. Count is 0 if the item doesn't exist in
--   the bag.
count :: Ord k => k -> Bag k -> Int
count k (MkBag m) = Map.findWithDefault 0 k m

-- | `isSubsetOf a b` = forall k. `count k a <= count k b`
isSubsetOf, isProperSubsetOf :: (Ord k) => Bag k -> Bag k -> Bool
isSubsetOf a b = uniqueLength a <= uniqueLength b && freqsLE (toFreqs a) (toFreqs b)
isProperSubsetOf a b = uniqueLength a <= uniqueLength b && freqsLT (toFreqs a) (toFreqs b)

freqsLE, freqsLT :: Ord k => [(k, Int)] -> [(k, Int)] -> Bool
freqsLE [] _ = True
freqsLE (_:_) [] = False
freqsLE ((a,n):as) ((b,m):bs)
  | a < b     = False
  | a == b    = n <= m && freqsLE as bs
  | otherwise = freqsLE ((a,n):as) bs
freqsLT [] [] = False
freqsLT [] (_:_) = True
freqsLT (_:_) [] = False
freqsLT ((a,n):as) ((b,m):bs)
  | a < b          = False
  | a == b, n > m  = False
  | a == b, n == m = freqsLT as bs
  | a == b, n < m  = freqsLE as bs
  | otherwise      = freqsLE ((a,n):as) bs

-- * Construction

-- | /O(log(n))/ Insert a item to a bag. Increases count of that item by 1.
insert :: Ord k => k -> Bag k -> Bag k
insert k (MkBag m) = MkBag $ Map.insertWith (+) k 1 m

-- | /O(log(n))/ Delete a item from a bag if exists. Decreases count of that item
--   by 1, if there was one at least.
delete :: Ord k => k -> Bag k -> Bag k
delete k (MkBag m) = MkBag $ Map.updateWithKey (\_ n -> positiveInt (pred n)) k m

-- | /O(log(n))/ Deletes one item from a bag. If the item doesn't exist in the bag,
--   returns @Nothing@. Otherwise, returns the bag after the removal.
pullOut :: Ord a => a -> Bag a -> Maybe (Bag a)
pullOut x (MkBag m) = case Map.updateLookupWithKey (\_ n -> positiveInt (pred n)) x m of
  (Nothing, _) -> Nothing
  (Just _,  m') -> Just (MkBag m')

-- * Combine

-- | `union a b` is a minimum bag `c` such that `a \`isSubsetOf\` c`
--   and `b \`isSubsetOf\` c`.
union :: (Ord k) => Bag k -> Bag k -> Bag k
union (MkBag a) (MkBag b) = MkBag $ Map.unionWith max a b

-- | `intersection a b` is a maximum bag `c` such that `c \`isSubsetOf\` a`
--   and `c \`isSubsetOf\` b`.
intersection :: (Ord k) => Bag k -> Bag k -> Bag k
intersection (MkBag a) (MkBag b) =
  MkBag $ Map.intersectionWith min a b

-- | `difference a b` is a minimum bag `c` such that
--   `a \`isSubsetOf\` append b c`
difference :: (Ord k) => Bag k -> Bag k -> Bag k
difference (MkBag a) (MkBag b) =
  MkBag $ Map.differenceWith (\n m -> positiveInt (n - m)) a b

-- | `cartesianProduct a b` is a bag consists of tuples `(x,y)`
--   where `x` is from `a` and `y` is from `b`, and for any `(x,y)`
--   `count (x,y) (cartesianProduct a b) = count x a * count y b`.
cartesianProduct :: (Ord j, Ord k) => Bag j -> Bag k -> Bag (j,k)
cartesianProduct a b =
  MkBag $ Map.fromDistinctAscList
    [ ((x,y), n*m) | (x,n) <- toAscFreqs a
                   , (y,m) <- toAscFreqs b ]

-- | O(k)
fromList :: Ord a => [a] -> Bag a
fromList = F.foldl' (flip insert) empty

-- | O(k)
fromAscList, fromDescList :: Eq a => [a] -> Bag a
fromAscList = MkBag . Map.fromDistinctAscList . runLength
fromDescList = MkBag . Map.fromDistinctDescList . runLength

runLength :: Eq a => [a] -> [(a,Int)]
runLength [] = []
runLength (a:as) = loop 1 as
  where
    loop !n (x : xs) | a == x = loop (succ n) xs
    loop n xs                 = (a,n) : runLength xs

toList, toAscList, toDescList :: Bag a -> [a]
toList = toAscList
toAscList = (\(a,n) -> replicate n a) <=< toAscFreqs
toDescList = (\(a,n) -> replicate n a) <=< toDescFreqs

-- | O(k)
fromDistinctAscList, fromDistinctDescList :: [a] -> Bag a
fromDistinctAscList = MkBag . Map.fromDistinctAscList . map (, 1)
fromDistinctDescList = MkBag . Map.fromDistinctDescList . map (, 1)
