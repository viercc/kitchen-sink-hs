{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Span(
   Span(..), Function(..),
   module Data.Type.Equality,
   Some(..)
) where

import Data.Kind
import Data.Type.Equality ((:~:)(..))
import Data.Some (Some(..))

type Span :: (j -> Type) -> (k -> Type) -> (j -> k -> Type) -> Constraint
class Span s t f | f -> s t where
    dom :: f a b -> s a
    cod :: f a b -> t b

type Function :: (j -> Type) -> (k -> Type) -> (j -> k -> Type) -> Constraint
class Span s t f => Function s t f | f -> s t where
    isFunction :: f a b -> f a b' -> b :~: b'
    apply :: s a -> Some (f a)