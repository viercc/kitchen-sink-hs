{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lattice.BitSet(BitSet(..)) where

import Lattice.Classes

import qualified Data.Bits as Bits
import Data.Bits(Bits((.|.), (.&.)))

-- | Lattice structure of Bits as bit set.
newtype BitSet a = BitSet { getBitSet :: a }
                 deriving (Show,Read,Eq,
                           Enum,Bounded,
                           Bits,Bits.FiniteBits)

instance Bits a => Meet (BitSet a) where
  (/\) = (.&.)
instance Bits a => Join (BitSet a) where
  (\/) = (.|.)

instance Bits a => HasTop (BitSet a) where
  top = complement bottom
instance Bits a => HasBottom (BitSet a) where
  bottom = Bits.zeroBits

instance Bits a => Lattice (BitSet a)
instance Bits a => LatticeBounded (BitSet a)
instance Bits a => LatticeDistributive (BitSet a)

instance Bits a => LatticeDiff (BitSet a) where
  (\\) = diffDefault
  xor = Bits.xor

instance Bits a => Heyting (BitSet a) where
  imp = impDefault
  eqv x y = Bits.complement (Bits.xor x y)

instance Bits a => LatticeComplement (BitSet a) where
  complement = Bits.complement
instance Bits a => Boolean (BitSet a)

