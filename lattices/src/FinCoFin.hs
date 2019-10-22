{-# LANGUAGE RankNTypes #-}
module FinCoFin where

import qualified Data.Set as Set

import           Lattice

-- | @FCFSet a@ is a finite or cofinite set of elements of the type @a@.

data FCFSet a = Fin !(Set.Set a) | CoFin !(Set.Set a)
              deriving (Show, Read, Eq)

instance Ord a => Meet (FCFSet a) where
  (/\) = intersection
instance Ord a => Join (FCFSet a) where
  (\/) = union
instance HasTop (FCFSet a) where
  top = universe
instance HasBottom (FCFSet a) where
  bottom = FinCoFin.empty
instance Ord a => Lattice (FCFSet a)
instance Ord a => LatticeBounded (FCFSet a)
instance Ord a => LatticeDistributive (FCFSet a)

instance Ord a => Heyting (FCFSet a) where
  imp = impDefault
  x `eqv` y = complement (x `xor` y)
instance Ord a => LatticeDiff (FCFSet a) where
  (\\) = diffDefault
  xor  = symdiff
instance Ord a => LatticeComplement (FCFSet a) where
  complement (Fin xs)   = CoFin xs
  complement (CoFin xs) = Fin xs
instance Ord a => Boolean (FCFSet a)

-- * Query

-- | Membership test.
member, notMember :: (Ord a) => a -> FCFSet a -> Bool
member x (Fin posi)   = Set.member x posi
member x (CoFin nega) = Set.notMember x nega

notMember x xs = not (member x xs)

-- | Is given finite set is subset of an FCFSet?
isSubsetOf :: (Ord a) => FCFSet a -> FCFSet a -> Bool
isSubsetOf (Fin xs)    (Fin ys)    = Set.isSubsetOf xs ys
isSubsetOf (CoFin _)   (Fin _)     = False
isSubsetOf (Fin xs)    (CoFin ys') = Set.null (xs /\ ys')
isSubsetOf (CoFin xs') (CoFin ys') = Set.isSubsetOf ys' xs'

-- * Construction
-- | Empty and universe sets.
empty, universe :: FCFSet a
empty    = Fin Set.empty
universe = CoFin Set.empty

-- | A singleton set.
singleton :: a -> FCFSet a
singleton x = Fin (Set.singleton x)

-- | Construct a set which only has members from a list.
fromList :: (Ord a) => [a] -> FCFSet a
fromList xs = Fin (Set.fromList xs)

-- | Insert an element.
insert :: (Ord a) => a -> FCFSet a -> FCFSet a
insert x (Fin posi)   = Fin $ Set.insert x posi
insert x (CoFin nega) = CoFin $ Set.delete x nega

-- | Delete an element.
delete :: (Ord a) => a -> FCFSet a -> FCFSet a
delete x (Fin posi)   = Fin $ Set.delete x posi
delete x (CoFin nega) = CoFin $ Set.insert x nega

-- * Combine

-- | Union.
union :: (Ord a) => FCFSet a -> FCFSet a -> FCFSet a
union xs ys = complement (complement xs `intersection` complement ys)

-- | Intersection.
intersection :: (Ord a) => FCFSet a -> FCFSet a -> FCFSet a
intersection (Fin xs)    (Fin ys)    = Fin (xs /\ ys)
intersection (Fin xs)    (CoFin ys') = Fin (xs \\ ys')
intersection (CoFin xs') (Fin ys)    = Fin (ys \\ xs')
intersection (CoFin xs') (CoFin ys') = CoFin (xs' \/ ys')

-- | Set difference.
difference :: (Ord a) => FCFSet a -> FCFSet a -> FCFSet a
difference xs ys = xs `intersection` complement ys

-- | Symmetric difference, or "XOR"
symdiff :: (Ord a) => FCFSet a -> FCFSet a -> FCFSet a
symdiff (Fin xs)    (Fin ys)    = Fin (xs `xor` ys)
symdiff (Fin xs)    (CoFin ys') = CoFin (xs `xor` ys')
symdiff (CoFin xs') (Fin ys)    = CoFin (xs' `xor` ys)
symdiff (CoFin xs') (CoFin ys') = Fin (xs' `xor` ys')

-- | Simpler implementation of symdiff
symdiff' :: (Ord a) => FCFSet a -> FCFSet a -> FCFSet a
symdiff' xs ys = (xs `difference` ys) `union` (ys `difference` xs)
