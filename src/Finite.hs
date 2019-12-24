{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDerivings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Finite where

import Data.Void
import Numeric.Natural
import GHC.Generics

class Finite a where
  card :: Natural
  toFinite :: Natural -> a
  fromFinite :: a -> Natural

outOfBounds :: forall a. (Finite a) => Natural -> a
outOfBounds n = error $
  "out of bounds (" ++ show n ++ ">=" ++ show (card @a) ++ ")

type N0 = Void
type N1 = ()
type N2 = Bool

instance Finite N0 where
  card = 0
  toFinite = outOfBounds
  fromFinite = absurd

instance Finite N1 where
  card = 1
  toFinite 0 = ()
  toFinite n = outOfBounds n
  fromFinite = const 0

instance Finite N2 where
  card = 2
  toFinite 0 = False
  toFinite 1 = True
  toFinite n = outOfBounds n
  fromFinite b = if b then 1 else 0

deriving instance Finite a => Finite (K1 a x)

instance (Finite (f x), Finite (g x)) => Finite (f :+: g) x where
  card = card @(f x) + card @(g x)
  toFinite n
    | n < card @(f x) = L1 (toFinite n)
    | n < card @((f :+: g) x) = R1 (toFinite (n - card @(f x)))
    | otherwise = outOfBounds n
  fromFinite (L1 fx) = fromFinite fx
  fromFinite (R1 gx) = card @(f x) + fromFinite gx

instance (Finite (f x), Finite (g x)) => Finite (f :*: g) x where
  card = card @(f x) * card @(g x)
  toFinite n
    | n < cf * cg = let (q,r) = quotRem n cg in toFinite q :*: toFinite r
    | otherwise   = outOfBounds n
      where cf = card @(f x)
            cg = card @(g x)
  fromFinite (fx :*: gx) = fromFinite fx * card @(g x) + fromFinite gx

