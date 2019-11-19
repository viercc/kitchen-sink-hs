{-

This module is a collection of weird, unusual
kinds of Monad instances.

-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE DeriveTraversable #-}
module Monad.Esoteric where

import Data.Foldable
import Control.Applicative

import Data.List (unfoldr)

-- These are found by exhaustively searching
-- all functions of the type (forall a. F (F a) -> F a).

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

--------------------------------

-- Non empty zip(ish)-list.
-- by treating finite list as "converging" sequence.
-- By "converging", I mean, it repeats same value after
-- finite elements.

data Nezzle a = a :| [a]
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Applicative) via (WrappedMonad Nezzle)

headNezzle :: Nezzle a -> a
headNezzle (a :| _) = a

tailNezzle :: Nezzle a -> Nezzle a
tailNezzle (_ :| (a:as)) = a :| as
tailNezzle single        = single

instance Monad Nezzle where
  return a = a :| []
  a :| []      >>= k = k a
  a :| (a':as) >>= k =
    headNezzle (k a) :| toList ((a' :| as) >>= tailNezzle . k)

--------------------------------

-- Odd-lengthed list
-- 
-- Monad instance is same as []'s instance.
-- Because concat'ing odd number of odd-lengthed lists yields
-- odd-lengthed list, it's a monad.
-- 
-- "Even-lengthed" list can't have such an instance,
-- because the length of `return` can't be even.
data Odd a = Odd a (Even a)
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Applicative) via (WrappedMonad Odd)

data Even a = Nil | Even a (Odd a)
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

plusEE :: Even a -> Even a -> Even a
plusEE Nil ys = ys
plusEE (Even x xs) ys = Even x (plusOE xs ys)

plusOE :: Odd a -> Even a -> Odd a
plusOE (Odd x xs) ys = Odd x (plusEE xs ys)

plusEO :: Even a -> Odd a -> Odd a
plusEO Nil ys = ys
plusEO (Even x xs) ys = Odd x (plusOO xs ys)

plusOO :: Odd a -> Odd a -> Even a
plusOO (Odd x xs) ys = Even x (plusEO xs ys)

instance Monad Odd where
  return a = Odd a Nil
  ma >>= k = ostep ma
    where
      ostep (Odd x xs) = k x `plusOE` estep xs
      
      estep Nil         = Nil
      estep (Even x xs) = k x `plusOO` ostep xs

-- (3n+1)-lengthed list, (4n+1)-lengthed list, ...
-- are also Monads.

newtype List3Np1 a = List3Np1 [a]
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  -- Monad instance inherited from [] keeps invariant.
  deriving newtype (Applicative, Monad)

makeList3Np1 :: [a] -> Maybe (List3Np1 a)
makeList3Np1 as
  | n `rem` 3 == 1 = Just (List3Np1 as)
  | otherwise      = Nothing
  where n = length as

makeInftyList3Np1 :: (s -> (a, s)) -> s -> List3Np1 a
makeInftyList3Np1 f s = List3Np1 (unfoldr (Just . f) s)
