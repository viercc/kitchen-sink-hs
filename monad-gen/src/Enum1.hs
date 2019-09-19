{-# LANGUAGE RankNTypes, EmptyCase, ScopedTypeVariables, TypeOperators, TypeApplications #-}
{-# LANGUAGE DerivingVia, StandaloneDeriving  #-}
{-# LANGUAGE UndecidableInstances #-}
module Enum1(
  Enum1(..),
  CoEnum1(..),
  allNaturals,
  allPures,
  allJoins,
  allLiftA2,
  
  Generically(..),
  GEnum1'(),
  GCoEnum1'()
) where

import Control.Applicative (liftA2)

import GHC.Generics

import Data.Coerce
import Data.Proxy

import Data.Functor.Identity

import Vec


class Enum1 f where
  size1 :: Proxy f -> Int -> Int
  
  enum1 :: Vec a -> Vec (f a)

newtype Generically f p = Generically { unGenerically :: f p }

instance (Generic1 f, GEnum1' (Rep1 f)) => Enum1 (Generically f) where
  size1 _ = size1' @(Rep1 f) Proxy
  enum1 as = Generically . to1 <$> enum1' as

deriving via (Generically Identity) instance Enum1 Identity
deriving via (Generically Maybe) instance Enum1 Maybe
deriving via (Generically (f :.: g))
    instance (Functor f, Enum1 f, Enum1 g) => Enum1 (f :.: g)

class CoEnum1 f where
  cosize1 :: Proxy f -> (Int -> Int) -> Int
  coenum1 :: (Vec a -> Vec r) -> Vec (f a -> r)

instance (Generic1 f, GCoEnum1' (Rep1 f)) => CoEnum1 (Generically f) where
  cosize1 _ = cosize1' @(Rep1 f) Proxy
  coenum1 gen = (. from1 . unGenerically) <$> coenum1' gen

deriving via (Generically Identity) instance CoEnum1 Identity
deriving via (Generically Maybe) instance CoEnum1 Maybe
deriving via (Generically (f :.: g))
  instance (Functor f, CoEnum1 f, CoEnum1 g) => CoEnum1 (f :.: g)

-------------------------------------
-- Generics

class GEnum1' g where
  size1' :: Proxy g -> Int -> Int
  enum1' :: Vec a -> Vec (g a)

instance GEnum1' V1 where
  size1' _ _ = 0
  enum1' _ = mempty

instance GEnum1' U1 where
  size1' _ _ = 1
  enum1' _ = pure U1

instance GEnum1' Par1 where
  size1' _ n = n
  enum1' xs = coerce xs

instance (GEnum1' f) => GEnum1' (M1 i c f) where
  size1' _ n = size1' @f Proxy n
  enum1' xs = coerce (enum1' @f xs)

instance (Enum1 f) => GEnum1' (Rec1 f) where
  size1' _ = size1 @f Proxy
  enum1' xs = coerce (enum1 @f xs)

instance (GEnum1' f, GEnum1' g) => GEnum1' (f :+: g) where
  size1' _ n = size1' @f Proxy n + size1' @g Proxy n
  enum1' xs = (L1 <$> enum1' xs) <> (R1 <$> enum1' xs)

instance (GEnum1' f, GEnum1' g) => GEnum1' (f :*: g) where
  size1' _ n = size1' @f Proxy n * size1' @g Proxy n
  enum1' xs = (:*:) <$> enum1' xs <*> enum1' xs

instance (Enum1 f, GEnum1' g) => GEnum1' (f :.: g) where
  size1' _ = size1 @f Proxy . size1' @g Proxy
  enum1' xs = Comp1 <$> enum1 (enum1' xs)

--------------------------------------------
-- Co-enumeration

class GCoEnum1' f where
  cosize1' :: Proxy f -> (Int -> Int) -> Int
  coenum1' :: (Vec a -> Vec r) -> Vec (f a -> r)

instance GCoEnum1' V1 where
  cosize1' _ _ = 1
  coenum1' _ = pure (\v1 -> case v1 of { })

instance GCoEnum1' U1 where
  cosize1' _ s = s 0
  coenum1' gen = const <$> gen empty

instance GCoEnum1' Par1 where
  cosize1' _ s = s 1
  coenum1' gen = generate n f
    where n = length $ gen (pure undefined)
          f i (Par1 b) = gen (singleton b) ! i

instance (GCoEnum1' f) => GCoEnum1' (M1 i c f) where
  cosize1' _ = cosize1' @f Proxy
  coenum1' gen = coerce (coenum1' @f gen)

instance (CoEnum1 f) => GCoEnum1' (Rec1 f) where
  cosize1' _ = cosize1 @f Proxy
  coenum1' gen = coerce (coenum1 @f gen)

instance (GCoEnum1' f, GCoEnum1' g) => GCoEnum1' (f :+: g) where
  cosize1' _ s = cosize1' @f Proxy s * cosize1' @f Proxy s
  coenum1' gen = merge <$> coenum1' gen <*> coenum1' gen
    where merge f _ (L1 fb) = f fb
          merge _ g (R1 gb) = g gb

instance (GCoEnum1' f, GCoEnum1' g) => GCoEnum1' (f :*: g) where
  cosize1' _ s = cosize1' @f Proxy (\n -> cosize1' @g Proxy (\m -> s (n + m)))
  coenum1' gen = uncurry1 <$> coenum1' (\as1 -> coenum1' (\as2 -> gen (as1 <> as2)))
    where uncurry1 k (fa :*: ga) = k fa ga

instance (CoEnum1 f, GCoEnum1' g) => GCoEnum1' (f :.: g) where
  cosize1' _ s = cosize1 @f Proxy $ cosizeVec1 @g Proxy s
  coenum1' gen = conv <$> coenum1 (coenumVec1 gen)
    where conv k = k . unComp1

cosizeVec1 :: forall g. (GCoEnum1' g) => Proxy g -> (Int -> Int) -> Int -> Int
cosizeVec1 _ s n = go 0 0
  where
    go i acc | i >= n    = s acc
             | otherwise = cosize1' @g Proxy $ \m -> go (i+1) (acc + m)

coenumVec1 :: forall g a r. (GCoEnum1' g) => (Vec a -> Vec r) -> Vec (g a) -> Vec r
coenumVec1 gen gs = go 0 empty
  where
    n = length gs
    go i acc | i >= n    = gen acc
             | otherwise = fmap ($ gs ! i) $ coenum1' (\as -> go (i + 1) (acc <> as))

---------------------------

allNaturals :: forall f g a. (CoEnum1 f, Enum1 g) => Vec (f a -> g a)
allNaturals = coenum1 enum1

coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce

allPures :: forall f a. (Enum1 f) => Vec (a -> f a)
allPures = coerceMap (. Identity) $ allNaturals @Identity @f

allJoins :: forall f a. (Functor f, CoEnum1 f, Enum1 f) => Vec (f (f a) -> f a)
allJoins = coerceMap (. Comp1) $ allNaturals @(f :.: f) @f

allLiftA2 :: forall f a b c. (Functor f, CoEnum1 f, Enum1 f) => (a -> b -> c) -> Vec (f a -> f b -> f c)
allLiftA2 f = coenum1 $ \as -> coenum1 $ \bs -> enum1 (liftA2 f as bs)
