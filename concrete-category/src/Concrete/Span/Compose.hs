
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Concrete.Span.Compose where

import Data.Kind

import Concrete.Span

type Compose :: (j -> k -> Type) -> (k -> l -> Type) -> (j -> l -> Type)
data Compose f g a b where
    Compose :: f a b -> g b c -> Compose f g a c

instance (Span s t f, Span t u g) => Span s u (Compose f g) where
    dom (Compose f _) = dom f
    cod (Compose _ g) = cod g

instance (Function s t f, Function t u g) => Function s u (Compose f g) where
    isFunction (Compose f g) (Compose f' g') = case isFunction f f' of
        Refl -> isFunction g g'
    apply a = case apply a of
        Some fa -> case apply (cod fa) of
            Some gfa -> Some (Compose fa gfa)