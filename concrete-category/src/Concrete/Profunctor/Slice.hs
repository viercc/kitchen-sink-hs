
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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Concrete.Profunctor.Slice where

import Data.Kind

import Concrete.Category
import Concrete.Object
import Concrete.Profunctor
import Concrete.Profunctor.Rep

type Slice :: (j -> j -> Type) -> (k -> k -> Type) -> j -> j -> k -> Type
data Slice c d t a b = Slice (c a t) (Cod d b)

instance (Span c, Span d) => Span (Slice c d t) where
    type Dom (Slice c d t) = Dom c
    type Cod (Slice c d t) = Cod d
    dom (Slice p _) = dom p
    cod (Slice _ b) = b

instance (Category c, Category d) => Profunctor c d (Slice c d t) where
    lmap f (Slice p b) = Slice (f >>> p) b
    rmap g (Slice p _) = Slice p (cod g)

instance (Category c, Category d, IsObject (Ob c) t) => Representable c d (Slice c d t) where
    type Rep (Slice c d t) _ = t
    sieve (Slice p _) = p
    tabulate b p = Slice p b
    pullRep b = Slice (ident isObject) b


type Coslice :: (j -> j -> Type) -> (k -> k -> Type) -> k -> j -> k -> Type
data Coslice c d t a b = Coslice (Dom c a) (d t b)

instance (Span c, Span d) => Span (Coslice c d t) where
    type Dom (Coslice c d t) = Dom c
    type Cod (Coslice c d t) = Cod d
    dom (Coslice a _) = a
    cod (Coslice _ p) = cod p

instance (Category c, Category d) => Profunctor c d (Coslice c d t) where
    lmap f (Coslice _ p) = Coslice (dom f) p
    rmap g (Coslice a p) = Coslice a (p >>> g)

instance (Category c, Category d, IsObject (Ob d) t) => Corepresentable c d (Coslice c d t) where
    type Corep (Coslice c d t) _ = t
    cosieve (Coslice _ p) = p
    cotabulate a p = Coslice a p
    pushCorep a = Coslice a (ident isObject)