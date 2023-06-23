{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Concrete.Profunctor where

import Data.Kind

import Concrete.Span
import Concrete.Category

import Concrete.Span.Compose


type Profunctor :: (j -> j -> Type) -> (k -> k -> Type) -> (j -> k -> Type) -> Constraint
class (Span p, Category c, Category d, Dom p ~ Ob c, Cod p ~ Ob d) => Profunctor c d p | p -> c d where
    {-# MINIMAL (lmap, rmap) | dimap #-}
    lmap :: c a' a -> p a b -> p a' b
    lmap f p = dimap f (ident (cod p)) p

    rmap :: d b b' -> p a b -> p a b'
    rmap g p = dimap (ident (dom p)) g p
    
    dimap :: c a' a -> d b b' -> p a b -> p a' b'
    dimap f g = lmap f . rmap g

instance Profunctor (->) (->) (->) where
    lmap = (>>>)
    rmap = (<<<)
    dimap f g h = f >>> h >>> g

newtype Hom c a b = Hom { getHom :: c a b }
    deriving newtype (Span, Category)

instance (Category c) => Profunctor c c (Hom c) where
    lmap f (Hom h) = Hom (f >>> h)
    rmap g (Hom h) = Hom (h >>> g)
    dimap f g (Hom h) = Hom (f >>> h >>> g)

instance (Profunctor c d p, Profunctor d e q, Category c, Category d, Category e) => Profunctor c e (Compose p q) where
    lmap f (Compose p q) = Compose (lmap f p) q
    rmap g (Compose p q) = Compose p (rmap g q)
    dimap f g (Compose p q) = Compose (lmap f p) (rmap g q)

