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

type Span :: (j -> k -> Type) -> Constraint
class Span (f :: j -> k -> Type) where
    type Dom f :: j -> Type
    type Cod f :: k -> Type
    dom :: f a b -> Dom f a
    cod :: f a b -> Cod f b

type Function :: (j -> k -> Type) -> Constraint
class Span f => Function f where
    isFunction :: f a b -> f a b' -> b :~: b'
    apply :: Dom f a -> Some (f a)