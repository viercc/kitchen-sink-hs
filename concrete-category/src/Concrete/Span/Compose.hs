{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Span.Compose where

import Data.Kind

import Concrete.Span

type Compose :: (j -> k -> Type) -> (k -> l -> Type) -> (j -> l -> Type)
data Compose f g a b where
    Compose :: f a b -> g b c -> Compose f g a c

instance (Span f, Span g, Cod f ~ Dom g) => Span (Compose f g) where
    type Dom (Compose f g) = Dom f
    type Cod (Compose f g) = Cod g
    
    dom (Compose f _) = dom f
    cod (Compose _ g) = cod g

instance (Function f, Function g, Cod f ~ Dom g) => Function (Compose f g) where
    isFunction (Compose f g) (Compose f' g') = case isFunction f f' of
        Refl -> isFunction g g'
    apply a = case apply a of
        Some fa -> case apply (cod fa) of
            Some gfa -> Some (Compose fa gfa)