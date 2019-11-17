{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
module Targets where

import GHC.Generics
import Enum1

data F a = F0 | F2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically F)

data G a = G1 a | G2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically G)

data H a = H0 | H1 a | H2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically H)

data W a = W1_0 a | W1_1 a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically W)

data T a = T2_0 a a | T2_1 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically T)

data J a = J1_0 a | J1_1 a | J2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically J)
