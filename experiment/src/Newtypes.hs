{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Newtypes(
    WrappedIntegral(..)
  , Two(..)
) where

import Text.Read(Read(..))
import Data.Functor.Identity

import GHC.Generics (Generic, Generic1)

newtype WrappedIntegral a =
  WrapIntegral { unWrapIntegral :: a }
  deriving stock (Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Applicative, Monad) via Identity
  deriving (Eq, Ord, Enum, Bounded, Num, Real, Integral) via a

instance Integral a => Show (WrappedIntegral a) where
  show = show . toInteger

instance Num a => Read (WrappedIntegral a) where
  readPrec = fromInteger <$> readPrec

newtype Two = Two Bool
  deriving stock (Eq, Ord)
  deriving (Enum, Bounded) via Bool
  deriving (Show, Read) via (WrappedIntegral Two)

instance Num Two where
  fromInteger n = Two (odd n)
  Two a + Two b = Two (a /= b)
  negate = id
  abs = id
  signum = id
  Two a * Two b = Two (a && b)

instance Real Two where
  toRational = toRational . toInteger

instance Integral Two where
  toInteger (Two b) = if b then 1 else 0
  quotRem _ 0 = error "division by zero"
  quotRem x _ = (x,0)

