{-# LANGUAGE RankNTypes, EmptyCase, ScopedTypeVariables, TypeOperators, TypeApplications #-}
{-# LANGUAGE DerivingVia, StandaloneDeriving  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Enum1(
  Enum1(..),
  CoEnum1(..),
  allNaturals,
  allPures,
  allJoins,
  allLiftA2,

  steppedCoEnum1,
  
  Generically(..),
  GEnum1'(),
  GCoEnum1'()
) where

import Data.Foldable
import Control.Applicative (liftA2)

import GHC.Generics

import Data.Coerce

import Data.Functor.Identity

import Vec

-- Small utility!
coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce

-------------------

class Enum1 f where
  size1 :: Int -> Int
  enum1 :: Vec a -> Vec (f a)
  fromEnum1 :: Int -> (a -> Int) -> f a -> Int

newtype Generically f p = Generically { unGenerically :: f p }

instance (Generic1 f, GEnum1' (Rep1 f)) => Enum1 (Generically f) where
  size1 = size1' @(Rep1 f)
  enum1 as = Generically . to1 <$> enum1' as
  fromEnum1 n ia = fromEnum1' n ia . from1 . unGenerically

deriving via (Generically Identity) instance Enum1 Identity
deriving via (Generically Maybe) instance Enum1 Maybe

instance (Enum1 f, Enum1 g) => Enum1 (f :.: g) where
  size1 = size1 @f . size1 @g
  enum1 xs = coerceMap Comp1 $ enum1 (enum1 xs)
  fromEnum1 n ia = inv
    where
      gsize = size1 @g n
      inv (Comp1 fga) = fromEnum1 gsize (fromEnum1 n ia) fga

---------------------------------------

steppedCoEnum1
  :: forall f g a.
     (Enum1 f, Foldable f, Enum1 g, Traversable g)
  => Vec (Vec (f a -> g a))
steppedCoEnum1 = generate size outer
  where
    fs = enum1 @f (singleton ())
    gs = enum1 @g (singleton ())
    n = length gs
    slots = size1 @f 1
    size = n ^ slots
    indices i j
      | i == 0    = []
      | otherwise = let (j', k) = j `divMod` n
                    in k : indices (i-1) j'
    outer j = fmap toNat $ traverse inner $ vec $ Prelude.zip [0..] (indices slots j)
    inner (fIdx, gIdx) =
      let numArgs = length (fs ! fIdx)
          vars = generate numArgs id
      in traverse (const vars) (gs ! gIdx)
    toNat gxTable fa =
      let as = vec (toList fa)
          gx = gxTable ! fromEnum1 @f 1 (const 0) fa
      in (as !) <$> gx

------------------------------------------

class CoEnum1 f where
  cosize1 :: (Int -> Int) -> Int
  coenum1 :: (Vec a -> Vec r) -> Vec (f a -> r)

instance (Generic1 f, GCoEnum1' (Rep1 f)) => CoEnum1 (Generically f) where
  cosize1 = cosize1' @(Rep1 f)
  coenum1 gen = (. from1 . unGenerically) <$> coenum1' gen

deriving via (Generically Identity) instance CoEnum1 Identity
deriving via (Generically Maybe) instance CoEnum1 Maybe
deriving via (Generically (f :.: g))
  instance (Functor f, CoEnum1 f, CoEnum1 g) => CoEnum1 (f :.: g)

-------------------------------------
-- Generics

class GEnum1' g where
  size1' :: Int -> Int
  enum1' :: Vec a -> Vec (g a)
  fromEnum1' :: Int -> (a -> Int) -> g a -> Int

instance GEnum1' V1 where
  size1' _ = 0
  enum1' _ = mempty
  fromEnum1' _ _ v = case v of { }

instance GEnum1' U1 where
  size1' _ = 1
  enum1' _ = pure U1
  fromEnum1' _ _ _ = 0

instance GEnum1' Par1 where
  size1' n = n
  enum1' xs = coerce xs
  fromEnum1' _ ia (Par1 a) = ia a

instance (GEnum1' f) => GEnum1' (M1 i c f) where
  size1' = size1' @f
  enum1' xs = coerce (enum1' @f xs)
  fromEnum1' n ia = coerce (fromEnum1' @f n ia)

instance (Enum1 f) => GEnum1' (Rec1 f) where
  size1' = size1 @f
  enum1' xs = coerce (enum1 @f xs)
  fromEnum1' n ia = coerce (fromEnum1 @f n ia)

instance (GEnum1' f, GEnum1' g) => GEnum1' (f :+: g) where
  size1' n = size1' @f n + size1' @g n
  enum1' xs = (L1 <$> enum1' xs) <> (R1 <$> enum1' xs)
  fromEnum1' n ia = inv
    where
      inv (L1 fa) = fromEnum1' n ia fa
      inv (R1 ga) = size1' @f n + fromEnum1' n ia ga

instance (GEnum1' f, GEnum1' g) => GEnum1' (f :*: g) where
  size1' n = size1' @f n * size1' @g n
  enum1' xs = (:*:) <$> enum1' xs <*> enum1' xs
  fromEnum1' n ia = inv
    where
      lsize = size1' @f n
      inv (fa :*: ga) = fromEnum1' n ia fa + lsize * fromEnum1' n ia ga

instance (Enum1 f, GEnum1' g) => GEnum1' (f :.: g) where
  size1' = size1 @f . size1' @g
  enum1' xs = Comp1 <$> enum1 (enum1' xs)
  fromEnum1' n ia = inv
    where
      gsize = size1' @g n
      inv (Comp1 fga) = fromEnum1 gsize (fromEnum1' n ia) fga

--------------------------------------------
-- Co-enumeration

class GCoEnum1' f where
  cosize1' :: (Int -> Int) -> Int
  coenum1' :: (Vec a -> Vec r) -> Vec (f a -> r)

instance GCoEnum1' V1 where
  cosize1' _ = 1
  coenum1' _ = pure (\v1 -> case v1 of { })

instance GCoEnum1' U1 where
  cosize1' s = s 0
  coenum1' gen = const <$> gen empty

instance GCoEnum1' Par1 where
  cosize1' s = s 1
  coenum1' gen = generate n f
    where n = length $ gen (pure undefined)
          f i (Par1 b) = gen (singleton b) ! i

instance (GCoEnum1' f) => GCoEnum1' (M1 i c f) where
  cosize1' = cosize1' @f
  coenum1' gen = coerce (coenum1' @f gen)

instance (CoEnum1 f) => GCoEnum1' (Rec1 f) where
  cosize1' = cosize1 @f
  coenum1' gen = coerce (coenum1 @f gen)

instance (GCoEnum1' f, GCoEnum1' g) => GCoEnum1' (f :+: g) where
  cosize1' s = cosize1' @f s * cosize1' @g s
  coenum1' gen = merge <$> coenum1' gen <*> coenum1' gen
    where merge f _ (L1 fb) = f fb
          merge _ g (R1 gb) = g gb

instance (GCoEnum1' f, GCoEnum1' g) => GCoEnum1' (f :*: g) where
  cosize1' s = cosize1' @f $ \n -> cosize1' @g $ \m -> s (n + m)
  coenum1' gen = uncurry1 <$> coenum1' (\as1 -> coenum1' (\as2 -> gen (as1 <> as2)))
    where uncurry1 k (fa :*: ga) = k fa ga

instance (CoEnum1 f, GCoEnum1' g) => GCoEnum1' (f :.: g) where
  cosize1' = cosize1 @f . cosizeVec1 @g
  coenum1' gen = conv <$> coenum1 (coenumVec1 gen)
    where conv k = k . unComp1

cosizeVec1 :: forall g. (GCoEnum1' g) => (Int -> Int) -> Int -> Int
cosizeVec1 s n = go 0 0
  where
    go i acc | i >= n    = s acc
             | otherwise = cosize1' @g $ \m -> go (i+1) (acc + m)

coenumVec1 :: forall g a r. (GCoEnum1' g) => (Vec a -> Vec r) -> Vec (g a) -> Vec r
coenumVec1 gen gs = go 0 empty
  where
    n = length gs
    go i acc | i >= n    = gen acc
             | otherwise = fmap ($ gs ! i) $ coenum1' (\as -> go (i + 1) (acc <> as))

---------------------------

allNaturals :: forall f g a. (CoEnum1 f, Enum1 g) => Vec (f a -> g a)
allNaturals = coenum1 enum1

allPures :: forall f a. (Enum1 f) => Vec (a -> f a)
allPures = coerceMap (. Identity) $ allNaturals @Identity @f

allJoins :: forall f a. (Functor f, CoEnum1 f, Enum1 f) => Vec (f (f a) -> f a)
allJoins = coerceMap (. Comp1) $ allNaturals @(f :.: f) @f

allLiftA2 :: forall f a b c. (Functor f, CoEnum1 f, Enum1 f) => (a -> b -> c) -> Vec (f a -> f b -> f c)
allLiftA2 f = coenum1 $ \as -> coenum1 $ \bs -> enum1 (liftA2 f as bs)
