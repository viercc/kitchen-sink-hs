{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
module Data.PureSet.Tree(
  Set(),


) where

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.Ordered as OL
import Prelude hiding (succ)

import Data.PureSet.Class

-- | Invariant: @toList xs@ is sorted in descending order
data Set = Empty | Set :> Set
  deriving (Eq, Ord)

infixr 3 :>

instance Show Set where
  showsPrec = defaultShowsPrec

instance IsList Set where
  type Item Set = Set
  
  toList :: Set -> [Set]
  toList Empty = []
  toList (x :> xs) = x : toList xs

  fromList :: [Set] -> Set
  fromList = fromDistinctDescList . OL.nubSortBy descending

descending :: Ord a => a -> a -> Ordering
descending = flip compare

fromDistinctDescList :: [Set] -> Set
fromDistinctDescList = foldr (:>) Empty

instance SetModel Set where
  empty :: Set
  empty = Empty
  
  singleton :: Set -> Set
  singleton x = x :> Empty

  doubleton :: Set -> Set -> Set
  doubleton x y = case compare x y of
    LT -> y :> x :> Empty
    EQ -> x :> Empty
    GT -> x :> y :> Empty

  union :: Set -> Set -> Set
  union xs ys = fromDistinctDescList $ OL.unionBy descending (toList xs) (toList ys)

  bigUnion :: Set -> Set
  bigUnion = treefold union Empty . toList

  intersection :: Set -> Set -> Set
  intersection xs ys = fromDistinctDescList $ OL.isectBy descending (toList xs) (toList ys)

  difference :: Set -> Set -> Set
  difference xs ys = fromDistinctDescList $ OL.minusBy descending (toList xs) (toList ys)

  symdiff :: Set -> Set -> Set
  symdiff xs ys = fromDistinctDescList $ OL.xunionBy descending (toList xs) (toList ys)

treefold :: (a -> a -> a) -> a -> [a] -> a
treefold op z = go
  where
    go [] = z
    go (x : xs) = treefoldNE op (x :| xs)

treefoldNE :: (a -> a -> a) -> NonEmpty a -> a
treefoldNE op = go
  where
    go (x :| []) = x
    go (x :| y : xs) = go (op x y :| pairs xs)

    pairs (x : y : xs') = op x y : pairs xs'
    pairs xs = xs
