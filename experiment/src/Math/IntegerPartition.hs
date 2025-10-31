{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Math.IntegerPartition(
  -- * Integer partition
  Partition(),

  -- ** Basic functions
  total, rank,
  distinctParts,
  singleton,

  -- ** Enumeration
  partitions,

  -- ** Refinement
  parents,
  searchRefinement,
  isRefinement,

  -- ** Visualization
  partitionsDot
) where

import GHC.IsList (IsList(..))

import qualified Data.IntMultiSet as Bag
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.Set as Set
import Data.Maybe (listToMaybe, isJust)
import Control.Monad (guard)
import HasseDiagram (dotHasse)

type Bag = Bag.IntMultiSet

newtype Partition = Partition Bag
  deriving stock (Eq, Ord)
  deriving newtype (Semigroup, Monoid)

instance Show Partition where
  showsPrec prec (Partition p) = showsPrec prec (Bag.toList p)

instance IsList Partition where
  type Item Partition = Int
  fromList :: [Int] -> Partition
  fromList as
    | any (<= 0) as = error $ "Partition.fromList: negative item " ++ show as
    | otherwise     = Partition $ Bag.fromList as
  
  toList :: Partition -> [Int]
  toList (Partition p) = Bag.toList p

-- | total = "sum of all parts"
total :: Partition -> Int
total (Partition p) = foldl' (\r (a,m) -> r + a * m) 0 $ Bag.toOccurList p

-- | rank = total - "number of parts"
--
-- @
-- 0 <= rank p <= total p - 1
-- @
rank :: Partition -> Int
rank (Partition p) = total (Partition p) - Bag.size p

distinctParts :: Partition -> IntSet
distinctParts (Partition p) = Bag.toSet p

singleton :: Int -> Partition
singleton n
  | n <= 0 = error "singleton: negative item"
  | otherwise = Partition $ Bag.singleton n

-- | Enumerate partitions of given total.
partitions :: Int -> [Partition]
partitions n0 = map fromList $ go n0 n0
  where
    go i n
      | n < 0 = []
      | n == 0 = [[]]
      | i <= 0 = []
      | i > n = go n n
      | otherwise =
          [i : rest | rest <- go i (n - i)]
            ++ go (i - 1) n

-- | Partitions which cover a given partition in
--   the refinement partial order.
--
-- - Preserves total
-- - Increases rank by 1
parents :: Partition -> Set Partition
parents (Partition p) = Set.fromList parentList
  where
    dupPairs = [(a,a) | (a,n) <- Bag.toOccurList p, n >= 2 ]
    distinctPairs = unorderedPairs (Bag.distinctElems p)
    partPairs = dupPairs ++ distinctPairs
    parentList = do
      (a,b) <- partPairs
      pure $ Partition $ Bag.insert (a + b) $ Bag.delete a $ Bag.delete b p

unorderedPairs :: [a] -> [(a,a)]
unorderedPairs [] = []
unorderedPairs (a:as) = [(a,b) | b <- as] ++ unorderedPairs as

-- | Searches a witness of refinement relation between partitions.
-- 
-- @'searchRefinement' p q@ tries to find a refinement witness of @q@ into @p@,
-- which is, a list of partitions @re :: [Partition]@ such that
--
-- - @p == mconcat re@
--   
--   @p@ is the union of all partitions in the list
--
-- - @q == 'fromList' ('total' <$> re)@
--
--   @q@ is the partition which has the parts of totals of elements in the list
--
-- If there is at least one such @re@, return @Just re@. Otherwise, return @Nothing@.
-- A witness of refinement is not necessarily unique, and this function chooses
-- one arbitrarily.
--
-- [Note]
-- 
-- This function can take many resources (time/memory) to compute.
--
-- Finding (and even deciding) refinement relation is known to be
-- NP-complete, and this implementation is not even the fastest one.
searchRefinement :: Partition -> Partition -> Maybe [Partition]
searchRefinement pp qq
  | total pp /= total qq = Nothing
  | otherwise = case compare (rank pp) (rank qq) of
      GT -> Nothing
      EQ | pp == qq -> Just [ singleton a | a <- toList pp ]
         | otherwise -> Nothing
      LT -> searchRefinementBody pp qq
  where
    searchRefinementBody :: Partition -> Partition -> Maybe [Partition]
    searchRefinementBody (Partition p) (Partition q) =
        fmap recover $ listToMaybe $ go [] p' np (Bag.toList q') nq 0 Bag.empty
      where
        common = Bag.intersection p q
        p' = p Bag.\\ common
        np = Bag.size p'
        q' = q Bag.\\ common
        nq = Bag.size q'
        
        commonParts = [Bag.singleton a | a <- Bag.toList common]
        recover refinement = Partition <$> (commonParts ++ refinement)

    go :: [Bag] -> Bag -> Int -> [Int] -> Int -> Int -> Bag -> [[Bag]]
    go acc p' np qs nq q_prev s_prev
      | np < 2 * nq = []
      | otherwise = case qs of
          [] -> [acc]
          q : qs' -> do
            s <- subsetsOfTotal q p'
            -- To avoid the double-counting,
            -- multiple subsets having the same total
            -- must be in non-increasing order
            -- (in whatever total order; here Bag's Ord instance. does
            -- not need to be related to refinement.)
            guard $ q_prev /= q || s <= s_prev 
            let np' = np - Bag.size s
            go (s : acc) (p' Bag.\\ s) np' qs' (nq - 1) q s

-- | Judges refinement relation between partitions.
--
-- [Note]
-- 
-- This function can take many resources (time/memory) to compute.
--
-- Finding (and even deciding) refinement relation is known to be
-- NP-complete, and this implementation is not even the fastest one.
isRefinement :: Partition -> Partition -> Bool
isRefinement p q = isJust (searchRefinement p q)

-- | Outputs a Hasse diagram (of refinement poset) for partitions of @n@,
--   expressed in DOT language (refer Graphviz documentation for DOT)
partitionsDot :: Int -> String
partitionsDot n0 = dotHasse (partitions n0) show (Set.toList . parents)

----

subsetsOfTotal :: Int -> Bag -> [Bag]
subsetsOfTotal = \n p -> go Bag.empty n (Bag.toOccurList p)
  where
    go s n p
      | n < 0 = []
      | n == 0 = [s]
      | otherwise = case p of
          []       -> []
          [(a,c)]  -> case quotRem n a of
            (k,r) -> [ Bag.insertMany a k s | k <= c, r == 0 ]
          (a,c):p' -> do
            k <- [0 .. min c (n `div` a)]
            let s' = Bag.insertMany a k s
                n' = n - a * k
            go s' n' p'