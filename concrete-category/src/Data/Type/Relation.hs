{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Relation where

import Control.Applicative (Applicative (..))
import Data.Functor.Classes (Eq1 (..), Eq2 (..))
import Data.Kind (Constraint, Type)
import Data.Maybe (isJust)
import Data.Some (Some (..))
import Data.Type.Equality (TestEquality (..), (:~:) (..))

type TestEquality2 :: (j -> k -> Type) -> Constraint
class TestEquality2 f where
  testEquality2 :: f a b -> f a' b' -> Maybe (a :~: a', b :~: b')

type Relation :: (j -> Type) -> (k -> Type) -> (j -> k -> Type) -> Constraint
class (TestEquality src, TestEquality dst, TestEquality2 f) => Relation src dst f | f -> src dst where
  src :: f a b -> src a
  dst :: f a b -> dst b

type Function :: (j -> Type) -> (k -> Type) -> (j -> k -> Type) -> Constraint
class (Relation src dst f) => Function src dst f | f -> src dst where
  isFunction :: f a b -> f a b' -> b :~: b'
  apply :: src a -> Some (f a)

type ZeroRel :: (j -> Type) -> (k -> Type) -> (j -> k -> Type)
data ZeroRel src dst a b
  deriving (Show, Eq, Ord)

instance Eq1 (ZeroRel src dst a) where
  liftEq _ r = case r of {}

instance Eq2 (ZeroRel src dst) where
  liftEq2 _ _ r = case r of {}

instance TestEquality2 (ZeroRel src dst) where
  testEquality2 r = case r of {}

instance (TestEquality src, TestEquality dst) => Relation src dst (ZeroRel src dst) where
  src r = case r of {}
  dst r = case r of {}

type FullRel :: (j -> Type) -> (k -> Type) -> (j -> k -> Type)
data FullRel src dst a b = FullRel !(src a) !(dst b)
  deriving (Show, Eq, Ord)

instance (TestEquality src, TestEquality dst) => TestEquality2 (FullRel src dst) where
  testEquality2 (FullRel a b) (FullRel a' b') = liftA2 (,) (testEquality a a') (testEquality b b')

instance (TestEquality src, TestEquality dst) => Relation src dst (FullRel src dst) where
  src (FullRel a _) = a
  dst (FullRel _ b) = b

type IdRel :: (k -> Type) -> (k -> k -> Type)
data IdRel ob a b where
  IdRel :: !(ob a) -> IdRel ob a a

instance (TestEquality ob) => Eq (IdRel ob a b) where
  _ == _ = True

instance (TestEquality ob) => Eq1 (IdRel ob a) where
  liftEq _ _ _ = True

instance (TestEquality ob) => Eq2 (IdRel ob) where
  liftEq2 :: (TestEquality ob) => (a -> b -> Bool) -> (c -> d -> Bool) -> IdRel ob a c -> IdRel ob b d -> Bool
  liftEq2 _ _ (IdRel a) (IdRel a') = isJust $ testEquality a a'

instance (TestEquality ob) => TestEquality2 (IdRel ob) where
  testEquality2 (IdRel a) (IdRel a') = testEquality a a' >>= \Refl -> Just (Refl, Refl)

instance (TestEquality ob) => Relation ob ob (IdRel ob) where
  src (IdRel a) = a
  dst (IdRel a) = a

instance (TestEquality ob) => Function ob ob (IdRel ob) where
  isFunction (IdRel _) (IdRel _) = Refl
  apply a = Some (IdRel a)

type ComposeRel :: (i -> j -> Type) -> (j -> k -> Type) -> (i -> k -> Type)
data ComposeRel f g a c where
  ComposeRel :: !(f a b) -> !(g b c) -> ComposeRel f g a c

instance Eq (ComposeRel f g a c) where
  _ == _ = True

instance (Relation obA obB f, Relation obB obC g) => TestEquality2 (ComposeRel f g) where
  testEquality2 (ComposeRel f g) (ComposeRel f' g') =
    liftA2 (,) (testEquality (src f) (src f')) (testEquality (dst g) (dst g'))

instance (Relation obA obB f, Relation obB obC g) => Relation obA obC (ComposeRel f g) where
  src (ComposeRel f _) = src f
  dst (ComposeRel _ g) = dst g

instance (Function obA obB f, Function obB obC g) => Function obA obC (ComposeRel f g) where
  isFunction (ComposeRel f g) (ComposeRel f' g') =
    case isFunction f f' of Refl -> isFunction g g'
  apply a = case apply a of
    Some f -> case apply (dst f) of
      Some g -> Some (ComposeRel f g)