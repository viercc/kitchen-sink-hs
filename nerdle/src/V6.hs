{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
module V6 where

import Data.Functor.Rep
import Data.Distributive

data V6 a = V6 a a a a a a
   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Key = N0 | N1 | N2 | N3 | N4 | N5
   deriving (Eq, Ord, Show, Read, Enum, Bounded)

instance Distributive V6 where
  distribute = distributeRep

instance Representable V6 where
   type Rep V6 = Key
   
   index (V6 x0 x1 x2 x3 x4 x5) i = case i of
     N0 -> x0; N1 -> x1; N2 -> x2; N3 -> x3;
     N4 -> x4; N5 -> x5
   
   tabulate f = V6 (f N0) (f N1) (f N2) (f N3) (f N4) (f N5)
