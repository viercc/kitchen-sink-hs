-- Super-nested "Continuation Monad"
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
module Monad.SuperCont where

import Control.Monad
import Control.Applicative

import Data.Functor.Contravariant

import Data.Coerce
import Data.Functor.Compose

-- Just shorthands

cmap :: Contravariant f => (a -> b) -> f b -> f a
cmap = contramap

type (:^:) = Op

infixr 8 :^:

-- Continuation Monad as a nest of contravariant hom functor (_ -> r)
newtype Cont r a = Cont { runCont :: r :^: r :^: a }

unit :: forall r a. a -> r :^: r :^: a
unit a = coerce (\f -> f a :: r)

instance Functor (Cont r) where
    fmap f = Cont . cmap (cmap f) . runCont

instance Applicative (Cont r) where
    pure = coerce . unit @r
    (<*>) = ap

instance Monad (Cont r) where
    ma >>= f = join' (fmap f ma)
      where
        join' = Cont . cmap (unit @r) . runCont . fmap runCont

newtype Cont3 r a = Cont3 { runCont3 :: r :^: r :^: r :^: r :^: r :^: r :^: a }
  deriving Functor via (Compose (Cont r) (Compose (Cont r) (Cont r))) 

instance Applicative (Cont3 r) where
    pure = coerce . unit @r . unit @r . unit @r
    (<*>) = ap

instance Monad (Cont3 r) where
    ma >>= f = join' (fmap f ma)
      where
        cmap3 = cmap . cmap . cmap
        join' = Cont3 . cmap3 (unit @r) . cmap3 (unit @r) . cmap3 (unit @r) . runCont3 . fmap runCont3