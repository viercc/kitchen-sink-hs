{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lattice.Ordered(Ordered(..)) where

import           Lattice.Classes

-- | Lattice structure induced by total order, namely Ord class.
newtype Ordered a = Ordered { getOrdered :: a }
                    deriving (Show,Read,Eq,Ord,Enum,Bounded)

instance Ord a => Meet (Ordered a) where
  (/\) = min
instance Ord a => Join (Ordered a) where
  (\/) = max

instance (Ord a, Bounded a) => HasTop (Ordered a) where
  top = maxBound
instance (Ord a, Bounded a) => HasBottom (Ordered a) where
  bottom = minBound

instance Ord a => Lattice (Ordered a)
instance (Ord a, Bounded a) => LatticeBounded (Ordered a)
instance Ord a => LatticeDistributive (Ordered a)

instance (Ord a, Bounded a) => Heyting (Ordered a) where
  imp a b = if a <= b then top else b

instance (Ord a, Bounded a) => LatticeDiff (Ordered a) where
  a \\ b = if b <= a then a else bottom
