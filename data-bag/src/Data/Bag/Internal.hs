{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
module Data.Bag.Internal where

import Prelude hiding (null)
import qualified Data.Foldable as F
import Data.Semigroup ( mtimesDefault, Semigroup (..), Sum (..) )
import Control.DeepSeq ( NFData )
import Data.Functor.Classes
import Text.Read (Read(..))

import qualified Data.Map.Strict as Map

newtype Bag a = MkBag { bagImpl :: Map.Map a Int }
  deriving newtype (Eq, Ord, NFData)

-- * Queries

-- | /O(1)/ Is given bag empty?
null :: Bag a -> Bool
null (MkBag m) = Map.null m

-- | /O(n)/ Total number of items in the bag.
size :: Bag a -> Int
size (MkBag m) = F.foldl' (+) 0 m

-- * Construction

-- | A bag with no items.
empty :: Bag a
empty = MkBag Map.empty

-- | A bag with one item.
singleton :: a -> Bag a
singleton a = MkBag (Map.singleton a 1)

fromFreqs :: Ord a => [(a, Int)] -> Bag a
fromFreqs freqs = MkBag $ Map.fromListWith (+) $ filter (\(_,n) -> n > 0) freqs

toFreqs, toAscFreqs, toDescFreqs :: Bag a -> [(a,Int)]
toFreqs = toAscFreqs
toAscFreqs (MkBag m) = Map.toAscList m
toDescFreqs (MkBag m) = Map.toDescList m

fromFreqsMap :: Ord a => Map.Map a Int -> Bag a
fromFreqsMap = MkBag . Map.filter (> 0)

toFreqsMap :: Bag a -> Map.Map a Int
toFreqsMap (MkBag m) = m

-- | Appends two bags @a@ and @b@. The count of any item in the returned bag is
--   the sum of the counts for @a@ and @b@.
--
--   In other words, the following holds for any @x@.
--
--   > 'Data.Bag.count' x (append a b) == count x a + count x b
append :: Ord a => Bag a -> Bag a -> Bag a
append (MkBag m1) (MkBag m2) = MkBag $ Map.unionWith (+) m1 m2

-- | It behaves so that @foldMap f bag = foldMap f ('toAscList' bag)@ holds.
instance Foldable Bag where
  null = null
  length = size
  foldMap f (MkBag m) = Map.foldMapWithKey (\a n -> mtimesDefault n (f a)) m

instance Eq1 Bag where
  liftEq eq (MkBag m1) (MkBag m2) = liftEq2 eq (==) m1 m2

instance Ord1 Bag where
  liftCompare cmp (MkBag m1) (MkBag m2) = liftCompare2 cmp compare m1 m2

instance Show1 Bag where
  liftShowsPrec showsA showlA p bag = showParen (p > 10) $
      ("fromFreqs " ++) . liftShowList2 showsA showlA showsPrec showList (toFreqs bag)

instance Show a => Show (Bag a) where
    showsPrec = showsPrec1

instance (Ord a, Read a) => Read (Bag a) where
  readPrec = readUnaryWith readListPrec "fromFreqs" fromFreqs


instance Ord a => Semigroup (Bag a) where
  (<>) = append
  stimes n | n > 0     = \(MkBag m) -> MkBag (Map.map (stimesInt n) m)
           | otherwise = error $ "Semigroup(Bag _): negative exponent " ++ show (toInteger n)
    where
      stimesInt :: Integral b => b -> Int -> Int
      stimesInt b = getSum . stimes b . Sum

instance Ord a => Monoid (Bag a) where
  mempty = empty

-- * Internal utilities
positiveInt :: Int -> Maybe Int
positiveInt n | n > 0 = Just n
              | otherwise = Nothing
