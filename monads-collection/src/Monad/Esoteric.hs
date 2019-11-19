{-

This module is a collection of weird, unusual
kinds of Monad instances.

-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators     #-}
module Monad.Esoteric where

import Control.Applicative
import GHC.Generics ((:+:)(..))

data Span a = Point a | Span a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Applicative) via (WrappedMonad Span)

instance Monad Span where
  return = Point
  Point a >>= k = k a
  Span a a' >>= k =
    case (k a, k a') of
      (Point b,  Point b')  -> Span b b'
      (Point b,  Span _ b') -> Span b b'
      (Span b _, Point b')  -> Span b b'
      (Span b _, Span _ b') -> Span b b'

data Gold a = Zero | One a | Two a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Applicative) via (WrappedMonad Gold)

instance Monad Gold where
  return = One
  Zero    >>= _ = Zero
  One a   >>= k = k a
  Two a a' >>= k =
    case k a of
      Zero -> Zero
      One b -> case k a' of
        Zero     -> Two b b
        One b'   -> Two b b'
        Two b' _ -> Two b b'
      mb -> mb

data Twist a = T Bool a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Applicative) via (WrappedMonad Twist)

instance Monad Twist where
  return a = T False a a
  (>>=) = bind'
    where
      bind' ma k = join' $ fmap k ma 
      join' (T b (T c x00 x01) (T d x10 x11)) =
        case (b, c, d) of
          (False, False, False) -> T False x00 x11
          (False, False, True)  -> T False x00 x10
          (False, True,  False) -> T True  x11 x01
          (False, True,  True)  -> T True  x10 x01
          (True,  False, False) -> T True  x01 x10
          (True,  False, True)  -> T True  x01 x11
          (True,  True,  False) -> T True  x00 x10
          (True,  True,  True)  -> T True  x00 x11
