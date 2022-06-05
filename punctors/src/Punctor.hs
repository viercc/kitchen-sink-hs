{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UnicodeSyntax #-}
-- {-# LANGUAGE GHC2021 #-}
---- Or without using the latest addition of GHC2021:
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Punctor where

import Prelude hiding (id, (.), punmap)
import Control.Category

import Data.Kind
import Data.Functor.Compose
import Data.Bifunctor
import Data.Coerce
import Data.Functor.Sum

-- | A type family of \"functions\" for each kind
--   @k1 -> k2 -> ・・・ -> kn -> Type@.
--
--   > Fn Type a b     = a -> b
--   > Fn (j -> k) a b = Poly j k a b ~ ∀(x :: j). Fn k (a x) (b x)
--   
--   e.g.
-- 
--   > Fn (Type -> Type) a b ~ ∀x. a x -> b x
--   > Fn (Nat -> Type -> Type) a b ~ ∀n x. a n x -> b n x
type Fn :: ∀(k :: Type) -> k -> k -> Type
type family Fn k :: k -> k -> Type
type instance Fn Type = (->)
type instance Fn (j -> k) = Poly j k

newtype Poly j k (a :: j -> k) (b :: j -> k) = Poly { runPoly :: ∀x. Fn k (a x) (b x) }

instance (Category (Fn k)) => Category (Poly j k) where
    id = Poly id
    Poly f . Poly g = Poly (f . g)

-- | @'Punctor' (f :: j -> k)@ is a functor @f@ between
--   categories @Fn j@ and @Fn k@.
type Punctor :: forall (j :: Type) (k :: Type). (j -> k) -> Constraint
class Punctor (f :: j -> k) where
    -- | 'fmap' but for between categories @Fn j@ and @Fn k@.
    --   Note that for @f :: Type -> Type@, it's just @fmap@.
    --
    --   > punmap :: Fn Type a b -> Fn Type (f a) (f b)
    --   > punmap :: (a -> b)    -> (f a -> f b)
    --
    --   It should satisfy the functor laws, given
    --   each of @Fn j@ and @Fn k@ actually has a @Category@ instance.
    --
    --   > punmap id = id
    --   > punmap (f . g) = punmap f . punmap g
    punmap :: Fn j a b -> Fn k (f a) (f b)


-- | @Bifunctor f@ can be replaced with @(Punctor f, ∀a. Punctor (f a))@
bunmap ::
     (Punctor (f :: j -> k -> l), ∀a. Punctor (f a), Category (Fn l))
  => Fn j a a' -> Fn k b b' -> Fn l (f a b) (f a' b')
bunmap fnA fnB = runPoly (punmap fnA) . punmap fnB

-- | You can represent a 'Bifunctor' as two instances of @Punctor@
newtype FromBifunctor f a b = FromBifunctor (f a b)
  deriving Bifunctor via f
instance Bifunctor f => Punctor (FromBifunctor f) where
    punmap fnA = Poly $ first fnA
instance Bifunctor f => Punctor (FromBifunctor f a) where
    punmap = second

-- | Punctor can be defined for Higher-kinded data pattern
data BlogArticle f = MkBlogArticle
  { postDate :: f Int,
    articleContent :: f String }

instance Punctor BlogArticle where
    punmap fnF MkBlogArticle{postDate, articleContent} =
        MkBlogArticle{ 
            postDate = runPoly fnF postDate,
            articleContent = runPoly fnF articleContent
        }

-- More complex examples
instance Punctor (Compose :: (k -> Type) -> (j -> k) -> j -> Type) where
    punmap :: Fn (k -> Type) f f' -> Fn ((j -> k) -> j -> Type) (Compose f) (Compose f')
    punmap fnF = Poly $ Poly $ Compose . runPoly fnF . getCompose

instance Punctor f => Punctor (Compose f :: (j -> k) -> j -> Type) where
    punmap :: Fn (j -> k) g g' -> Fn (j -> Type) (Compose f g) (Compose f g')
    punmap fnG = Poly $ Compose . punmap (runPoly fnG) . getCompose

instance (Punctor f, Punctor g) => Punctor (Compose f g :: k -> Type) where
    punmap :: Fn k x x' -> Fn Type (Compose f g x) (Compose f g x')
    punmap fnX = Compose . punmap (punmap fnX) . getCompose

instance Punctor (Sum :: (k -> Type) -> (k -> Type) -> k -> Type) where
    punmap :: forall f f'. Fn (k -> Type) f f' -> Fn ((k -> Type) -> k -> Type) (Sum f) (Sum f')
    punmap fnF = Poly $ Poly onleft
      where
        onleft :: forall g x. Sum f g x -> Sum f' g x
        onleft (InL fx) = InL (runPoly fnF fx)
        onleft (InR gx) = InR gx

instance Punctor (Sum f :: (k -> Type) -> k -> Type) where
    punmap :: forall g g'. Fn (k -> Type) g g' -> Fn (k -> Type) (Sum f g) (Sum f g')
    punmap fnG = Poly onright
      where
        onright:: forall x. Sum f g x -> Sum f g' x
        onright (InL fx) = InL fx
        onright (InR gx) = InR (runPoly fnG gx)

instance (Punctor f, Punctor g) => Punctor (Sum (f :: k -> Type) g) where
    punmap :: forall x x'. Fn k x x' -> Fn Type (Sum f g x) (Sum f g x')
    punmap fnX = both
      where
        both (InL fx) = InL (punmap fnX fx)
        both (InR gx) = InR (punmap fnX gx)
