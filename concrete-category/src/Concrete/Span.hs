{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Concrete.Span(
   Span(..), Function(..),
   module Data.Type.Equality,
   Some(..)
) where

import Data.Kind
import Data.Type.Equality ((:~:)(..))
import Data.Some (Some(..))
import Data.Proxy

type Span :: (j -> k -> Type) -> Constraint
class Span (f :: j -> k -> Type) where
    type Dom f :: j -> Type
    type Cod f :: k -> Type
    dom :: f a b -> Dom f a
    cod :: f a b -> Cod f b

instance Span (->) where
    type Dom (->) = Proxy
    type Cod (->) = Proxy
    dom _ = Proxy
    cod _ = Proxy

type Function :: (j -> k -> Type) -> Constraint
class Span f => Function f where
    isFunction :: f a b -> f a b' -> b :~: b'
    apply :: Dom f a -> Some (f a)