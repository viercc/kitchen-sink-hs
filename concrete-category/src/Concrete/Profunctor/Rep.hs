
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
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Concrete.Profunctor.Rep where

import Data.Kind

import Concrete.Span
import Concrete.Category
import Concrete.Span.Compose
import Concrete.Profunctor
import Data.Proxy

-- * Representable

type Representable :: (j -> j -> Type) -> (k -> k -> Type) -> (j -> k -> Type) -> Constraint
class (Profunctor c d p) => Representable c d (p :: j -> k -> Type) | p -> c d where
    type Rep (p :: j -> k -> Type) (a :: k) :: j

    sieve :: p a b -> c a (Rep p b)
    tabulate :: Ob d b -> c a (Rep p b) -> p a b
    pullRep :: Ob d b -> p (Rep p b) b

obmapRep ::(Representable c d p) => Proxy p -> Ob d a -> Ob c (Rep p a)
obmapRep (_ :: Proxy p) a = dom (pullRep a :: p _ _)

fmapRep :: (Representable c d p) => Proxy p -> d a b -> c (Rep p a) (Rep p b)
fmapRep (_ :: Proxy p) g = sieve $ rmap g $ (pullRep (dom g) :: p _ _)

instance (Category c) => Representable c c (Hom c) where
    type Rep (Hom c) a = a
    
    sieve = getHom
    tabulate _ = Hom
    pullRep b = Hom (ident b)

instance
  (Category c, Category d, Category e, Representable c d p, Representable d e q)
  => Representable c e (Compose p q) where
    type Rep (Compose p q) a = Rep p (Rep q a)

    sieve (Compose p q) = sieve p >>> fmapRep (Proxy @p) (sieve q)
    tabulate b f =
        let b' = obmapRep (Proxy @q) b
            p = tabulate b' f
            q = tabulate b (ident b')
        in Compose p q
    
    pullRep b =
        let q = pullRep b
            p = pullRep (dom q)
        in Compose p q

-- * Corepresentable

type Corepresentable :: (j -> j -> Type) -> (k -> k -> Type) -> (j -> k -> Type) -> Constraint
class (Profunctor c d p) => Corepresentable c d (p :: j -> k -> Type) | p -> c d where
    type Corep (p :: j -> k -> Type) (a :: j) :: k

    cosieve :: p a b -> d (Corep p a) b
    cotabulate :: Ob c a -> d (Corep p a) b -> p a b
    pushCorep :: Ob c a -> p a (Corep p a)

obmapCorep ::(Corepresentable c d p) => Proxy p -> Ob c a -> Ob d (Corep p a)
obmapCorep (_ :: Proxy p) a = cod (pushCorep a :: p _ _)

fmapCorep :: (Corepresentable c d p) => Proxy p -> c a b -> d (Corep p a) (Corep p b)
fmapCorep (_ :: Proxy p) g = cosieve $ lmap g $ (pushCorep (cod g) :: p _ _)

instance (Category c) => Corepresentable c c (Hom c) where
    type Corep (Hom c) a = a
    
    cosieve = getHom
    cotabulate _ = Hom
    pushCorep a = Hom (ident a)

instance
  (Category c, Category d, Category e, Corepresentable c d p, Corepresentable d e q)
  => Corepresentable c e (Compose p q) where
    type Corep (Compose p q) a = Corep q (Corep p a)

    cosieve (Compose p q) = fmapCorep (Proxy @q) (cosieve p) >>> cosieve q
    cotabulate a f =
        let a' = obmapCorep (Proxy @p) a
            p = cotabulate a (ident a')
            q = cotabulate a' f
        in Compose p q
    
    pushCorep a =
        let p = pushCorep a
            q = pushCorep (cod p)
        in Compose p q
