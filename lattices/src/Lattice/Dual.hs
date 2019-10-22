module Lattice.Dual (Dual(..)) where

import Lattice.Classes

-- | Dual lattice.
newtype Dual a = Dual { getDual :: a }
               deriving (Show,Read,Eq)

instance Ord a => Ord (Dual a) where
  compare x y = compare (getDual y) (getDual x)

instance Bounded a => Bounded (Dual a) where
  minBound = Dual maxBound
  maxBound = Dual minBound

instance (Bounded a, Enum a) => Enum (Dual a) where
  succ = Dual . pred . getDual
  pred = Dual . succ . getDual
  toEnum = Dual . toEnumReversed
  fromEnum = fromEnumReversed . getDual

toEnumReversed :: (Bounded a, Enum a) => Int -> a
toEnumReversed n = x where
  x = toEnum (nmin + nmax - n)
  nmax = fromEnum (maxBound `asTypeOf` x)
  nmin = fromEnum (minBound `asTypeOf` x)

fromEnumReversed :: (Bounded a, Enum a) => a -> Int
fromEnumReversed x = nmin + nmax - fromEnum x where
  nmax = fromEnum (maxBound `asTypeOf` x)
  nmin = fromEnum (minBound `asTypeOf` x)

instance Join a => Meet (Dual a) where
  Dual x /\ Dual y = Dual (x \/ y)
instance Meet a => Join (Dual a) where
  Dual x \/ Dual y = Dual (x /\ y)
instance HasBottom a => HasTop (Dual a) where
  top = Dual bottom
instance HasTop a => HasBottom (Dual a) where
  bottom = Dual top

instance Lattice a => Lattice (Dual a)
instance LatticeBounded a => LatticeBounded (Dual a)
instance LatticeDistributive a => LatticeDistributive (Dual a)

instance Heyting a => LatticeDiff (Dual a) where
  Dual x \\ Dual y = Dual (y `imp` x)
  Dual x `xor` Dual y = Dual (x `eqv` y)

instance LatticeDiff a => Heyting (Dual a) where
  Dual x `imp` Dual y = Dual (y \\ x)
  Dual x `eqv` Dual y = Dual (x `xor` y)

instance LatticeComplement a => LatticeComplement (Dual a) where
  complement = Dual . complement . getDual
instance Boolean a => Boolean (Dual a)
