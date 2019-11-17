{-

This module is a collection of weird, unusual
kinds of Monad instances.

-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE DeriveTraversable #-}
module Monad.Esoteric where

import Control.Monad

data Span a = Point a | Span a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Applicative, Monad) via (WrappedMonad Gold)

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
  deriving (Applicative, Monad) via (WrappedMonad Gold)

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
  deriving (Applicative, Monad) via (WrappedMonad Gold)

instance Monad Twist where
  return a = T False a a
  ma >>= k = joinTwist (fmap k ma)
    where
      joinTwist (T b (T c x0 x1) (T d x2 x3)) =
        case (b, c, d) of
          (False, False, False) -> T False x0 x3
          (False, False, True)  -> T False x0 x2
          (False, True,  False) -> T True  x3 x1
          (False, True,  True)  -> T True  x2 x1
          (True,  False, False) -> T True  x1 x2
          (True,  False, True)  -> T True  x1 x3
          (True,  True,  False) -> T True  x0 x2
          (True,  True,  True)  -> T True  x0 x3
