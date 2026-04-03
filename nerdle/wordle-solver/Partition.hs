-- | Subset partition of finite set of integers
module Partition(
  Partition(),
  -- * Queries
  parts, partSizes, width, height, size,
  representatives,

  -- * Conversion
  toMap, fromMap, fromMapInt, fromVector,

  -- * Construction
  empty, discrete, indiscrete,
  restrict, exclude, delete, refine,
) where

import Data.Function (on)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Functor.Classes (Eq1(liftEq), Ord1 (liftCompare))
import Data.Maybe (mapMaybe)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map as Map
import qualified Data.Vector.Strict as V

-- | !!Internal only!! Part of a partition.
data Part = Part
  !Int    -- ^ Size of a part.
  !IntSet -- ^ Set of integers this part contains. Always nonempty.

partSize :: Part -> Int
partSize (Part n _) = n

partToSet :: Part -> IntSet
partToSet (Part _ xs) = xs

repr :: Part -> Int
repr (Part _ xs) = IntSet.findMin xs

-- Eq and Ord instance for Part is a specialized one for @Set Part@.
instance Eq Part where
  (==) = (==) `on` repr

instance Ord Part where
  compare = (compare `on` partSize) <> (compare `on` repr)

-- exact equality
eqPart :: Part -> Part -> Bool
eqPart (Part np p) (Part nq q) = np == nq && p == q

-- exact comparison
comparePart :: Part -> Part -> Ordering
comparePart (Part np p) (Part nq q) = compare np nq <> compare p q

newPart :: IntSet -> Maybe Part
newPart xs 
  | IntSet.null xs = Nothing
  | otherwise = Just $ Part (IntSet.size xs) xs

newtype Partition = Partition { unPartition :: Set Part }

instance Eq Partition where
  Partition ps == Partition qs = liftEq eqPart ps qs

instance Ord Partition where
  compare (Partition ps) (Partition qs) = liftCompare comparePart ps qs

-- * Queries

-- | /O(r)/ List of parts in a partition. All of the returned sets are
--   nonempty.
--   (the outer list can be empty for an empty partition.)
parts :: Partition -> [IntSet]
parts = map partToSet . Set.toList . unPartition 

-- | /O(r)/ List of sizes of parts in a partition. All elements are positive.
--
-- > partSizes ps == map IntSet.size (parts ps)
partSizes :: Partition -> [Int]
partSizes = map partSize . Set.toList . unPartition

-- | /O(1)/ width of a partition = number of parts it contains.
--
-- > width ps === length (parts ps)
width :: Partition -> Int
width = Set.size . unPartition

-- | /O(w)/ Total number of elements.
--
-- > size ps === sum (partSizes ps)
size :: Partition -> Int
size = sum . map partSize . Set.toList . unPartition

-- | /O(log(w))/ Size of the largest part. 0 for the empty partition.
--
-- > height ps === maximum (0 : partSizes ps)
height :: Partition -> Int
height = maybe 0 partSize . Set.lookupMax . unPartition

-- | /O(w)/ Smallest elements of each parts in a partition.
--
-- > representatives ps === map IntSet.findMin (parts ps)
representatives :: Partition -> [Int]
representatives = map repr . Set.elems . unPartition

-- * Conversion

-- | /O(n * log(n))/ Convert to a classification map.
toMap :: Partition -> IntMap Int
toMap = IntMap.unions . map (\p -> IntMap.fromSet (const (repr p)) (partToSet p)) . Set.toList . unPartition

-- | Convert from a classification map
fromMap :: (Ord a) => IntMap a -> Partition
fromMap classifier =
  Partition . Set.fromList . mapMaybe newPart . Map.elems $
    Map.fromListWith IntSet.union [ (a, IntSet.singleton i) | (i,a) <- IntMap.toList classifier ]

-- | Specialized 'fromMap'
fromMapInt :: IntMap Int -> Partition
fromMapInt classifier =
  Partition . Set.fromList . mapMaybe newPart . IntMap.elems $
    IntMap.fromListWith IntSet.union [ (a, IntSet.singleton i) | (i,a) <- IntMap.toList classifier ]

fromVector :: (Ord a) => V.Vector a -> Partition
fromVector classVec =
  Partition . Set.fromList . mapMaybe newPart . Map.elems $
    Map.fromListWith IntSet.union [ (a, IntSet.singleton i) | (i,a) <- V.toList (V.indexed classVec) ]

-- * Construction

empty :: Partition
empty = Partition Set.empty

indiscrete :: IntSet -> Partition
indiscrete xs = Partition $ foldMap Set.singleton (newPart xs)

discrete :: IntSet -> Partition
discrete xs = Partition $ Set.fromDistinctAscList [ Part 1 (IntSet.singleton x) | x <- IntSet.toAscList xs ]

restrict :: Partition -> IntSet -> Partition
restrict ps ys = Partition $ Set.fromList . mapMaybe (newPart . IntSet.intersection ys) $ parts ps

exclude :: Partition -> IntSet -> Partition
exclude ps ys = Partition $ Set.fromList . mapMaybe (newPart . (IntSet.\\ ys)) $ parts ps

-- | > delete x ps = exclude ps (IntSet.singleton x)
delete :: Int -> Partition -> Partition
delete x ps = loop [] (Set.toAscList (unPartition ps))
  where
    loop _ [] = ps -- no part contained x
    loop prev (p@(Part n xs) : next)
      | IntSet.member x xs =
          let p' = Part (n-1) (IntSet.delete x xs)
              -- @prev@ is list accumulating "miss" parts in reversed order.
              -- Since @next@ is distinct and in ascending order,
              -- @prev@ is distinct and descending order.
              prevSet = Set.fromDistinctDescList prev
              -- Because @p' < p@ by how we defined @Ord Part@, @p' : next@
              -- is ascending and distinct.
              -- (n > 1) checks p' is still nonempty after deletion.
              nextSet = Set.fromDistinctAscList ([p' | n > 1] ++ next)
          in Partition $ Set.union prevSet nextSet
      | otherwise = loop (p : prev) next

refine :: Partition -> IntSet -> Partition
refine ps ys = Partition $ Set.union (unPartition (restrict ps ys)) (unPartition (exclude ps ys))