{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
module V4 where

import Data.Functor.Rep
import Data.Distributive

data V4 a = V4 a a a a
   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Key = N0 | N1 | N2 | N3
   deriving (Eq, Ord, Show, Read, Enum, Bounded)

instance Distributive V4 where
  distribute = distributeRep

instance Representable V4 where
   type Rep V4 = Key
   
   index (V4 x0 x1 x2 x3) i = case i of
     N0 -> x0; N1 -> x1; N2 -> x2; N3 -> x3
   
   tabulate f = V4 (f N0) (f N1) (f N2) (f N3)
