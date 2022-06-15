{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
module V8 where

import Data.Functor.Rep
import Data.Distributive

data V8 a = V8 a a a a a a a a
   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Key = N0 | N1 | N2 | N3 | N4 | N5 | N6 | N7
   deriving (Eq, Ord, Show, Read, Enum, Bounded)

instance Distributive V8 where
  distribute = distributeRep

instance Representable V8 where
   type Rep V8 = Key
   
   index (V8 x0 x1 x2 x3 x4 x5 x6 x7) i = case i of
     N0 -> x0; N1 -> x1; N2 -> x2; N3 -> x3;
     N4 -> x4; N5 -> x5; N6 -> x6; N7 -> x7
   
   tabulate f = V8 (f N0) (f N1) (f N2) (f N3) (f N4) (f N5) (f N6) (f N7)
