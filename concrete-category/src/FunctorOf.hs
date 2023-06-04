{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module FunctorOf where

import Category
import Data.Coerce (coerce)
import Data.Kind (Constraint, Type)
import Data.Some (Some (..))
import Data.Type.Equality (TestEquality ())
import Data.Type.Relation

type FunctorOf :: (j -> j -> Type) -> (k -> k -> Type) -> (j -> k -> Type) -> Constraint
class (Category c, Category d, Function (Ob c) (Ob d) f) => FunctorOf c d f | f -> c d where
  fmapOf :: c a b -> Fmapped f d a b

data Fmapped f d a b where
  Fmapped :: !(f a fa) -> !(f b fb) -> !(d fa fb) -> Fmapped f d a b

makeFmapped ::
  forall c d f a b.
  (FunctorOf c d f) =>
  c a b ->
  (forall fa fb. f a fa -> f b fb -> d fa fb) ->
  Fmapped f d a b
makeFmapped x body = case (apply (dom x), apply (cod x)) of
  (Some fa, Some fb) -> Fmapped fa fb (body fa fb)

-- * Identity

newtype Id c a b = Id (IdRel (Ob c) a b)

deriving newtype instance
  (TestEquality (Ob c)) => TestEquality2 (Id c)

deriving newtype instance
  (ob ~ Ob c, TestEquality ob) => Relation ob ob (Id c)

deriving newtype instance
  (ob ~ Ob c, TestEquality ob) => Function ob ob (Id c)

instance (Category c) => FunctorOf c c (Id c) where
  fmapOf x = Fmapped (Id (IdRel (dom x))) (Id (IdRel (cod x))) x

-- * Discrete -> C

newtype FromDiscrete c a b = FromDiscrete (Id c a b)

deriving newtype instance
  (TestEquality (Ob c)) => TestEquality2 (FromDiscrete c)

deriving newtype instance
  (ob ~ Ob c, TestEquality ob) => Relation ob ob (FromDiscrete c)

deriving newtype instance
  (ob ~ Ob c, TestEquality ob) => Function ob ob (FromDiscrete c)

instance (Category c, Ob c ~ ob) => FunctorOf (Discrete ob) c (FromDiscrete c) where
  fmapOf (DiscreteIdent a) = Fmapped (coerce (IdRel a)) (coerce (IdRel a)) (ident a)

-- * C -> Indiscrete

newtype ToIndiscrete c a b = ToIndiscrete (Id c a b)

deriving newtype instance
  (TestEquality (Ob c)) => TestEquality2 (ToIndiscrete c)

deriving newtype instance
  (ob ~ Ob c, TestEquality ob) => Relation ob ob (ToIndiscrete c)

deriving newtype instance
  (ob ~ Ob c, TestEquality ob) => Function ob ob (ToIndiscrete c)

instance (Category c, Ob c ~ ob) => FunctorOf c (Indiscrete ob) (ToIndiscrete c) where
  fmapOf x = Fmapped (coerce (IdRel (dom x))) (coerce (IdRel (cod x))) (Indiscrete (dom x) (cod x))

-- * Composition

type Compose = ComposeRel

-- | Composition of "Function on objects". Composition is in diagrammatic order. (i.e. reverse of (.), same to (>>>))
instance (FunctorOf c d f, FunctorOf d e g) => FunctorOf c e (ComposeRel f g) where
  fmapOf x =
    case fmapOf x of
      Fmapped fa fb fx -> case fmapOf fx of
        Fmapped gfa gfb gfx ->
          Fmapped (ComposeRel fa gfa) (ComposeRel fb gfb) gfx