{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}

{- |

This module is a collection of weird, unusual
kinds of Monad instances.

-}
module Monad.Esoteric where

import Control.Applicative
import Control.Monad (ap, join)
import Data.List (unfoldr)

-- These are found by exhaustively searching
-- all functions of the type (forall a. F (F a) -> F a).

data Span a = Point a | Span a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Span where
  pure = Point
  (<*>) = ap

instance Monad Span where
  Point a >>= k = k a
  Span a a' >>= k =
    case (k a, k a') of
      (Point b, Point b') -> Span b b'
      (Point b, Span _ b') -> Span b b'
      (Span b _, Point b') -> Span b b'
      (Span b _, Span _ b') -> Span b b'

enumSpan :: (Alternative f) => f a -> f (Span a)
enumSpan as =
  Point <$> as
    <|> Span <$> as <*> as

data Gold a = Zero | One a | Two a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Gold where
  pure = One
  (<*>) = ap

instance Monad Gold where
  Zero >>= _ = Zero
  One a >>= k = k a
  Two a a' >>= k =
    case k a of
      Zero -> Zero
      One b -> case k a' of
        Zero -> Two b b
        One b' -> Two b b'
        Two b' _ -> Two b b'
      mb -> mb

enumGold :: (Alternative f) => f a -> f (Gold a)
enumGold as =
  pure Zero
    <|> One <$> as
    <|> Two <$> as <*> as

-- Twist is also found by searching.
-- What it means is not clear, but at least it passes Monad laws check.
data Twist a = T Bool a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Twist where
  pure a = T False a a
  (<*>) = ap

instance Monad Twist where
  (>>=) = bind'
    where
      bind' ma k = join' $ fmap k ma
      join' (T b (T c x00 x01) (T d x10 x11)) =
        case (b, c, d) of
          (False, False, False) -> T False x00 x11
          (False, False, True) -> T False x00 x10
          (False, True, False) -> T True x11 x01
          (False, True, True) -> T True x10 x01
          (True, False, False) -> T True x01 x10
          (True, False, True) -> T True x01 x11
          (True, True, False) -> T True x00 x10
          (True, True, True) -> T True x00 x11

enumTwist :: (Alternative f) => f a -> f (Twist a)
enumTwist as = T <$> (pure True <|> pure False) <*> as <*> as

-- Twist'
data Twist' a = T' Bool a a
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

isoTT' :: Twist a -> Twist' a
isoTT' (T b x0 x1) = if b then T' b x1 x0 else T' b x0 x1

isoT'T :: Twist' a -> Twist a
isoT'T (T' b x0 x1) = if b then T b x1 x0 else T b x0 x1

instance Applicative Twist' where
  pure a = T' False a a
  (<*>) = ap

{-
Transfer the instance Monad Twist via isoTT'

join' (T' b (T' c x0 x1) (T' d x10 x11))
 = isoTT' $ join . isoT'T . fmap isoT'T $ (T' b (T' c x00 x01) (T' d x10 x11))
 = case (b,c,d) of
     (False, False, False) -> isoTT' $ join $ T False (T False x00 x01) (T False x10 x11)
     (False, False, True)  -> isoTT' $ join $ T False (T False x00 x01) (T True  x11 x10)
     (False, True,  False) -> isoTT' $ join $ T False (T True  x01 x00) (T False x10 x11)
     (False, True,  True)  -> isoTT' $ join $ T False (T True  x01 x00) (T True  x11 x10)
     (True,  False, False) -> isoTT' $ join $ T True  (T False x10 x11) (T False x00 x01)
     (True,  False, True)  -> isoTT' $ join $ T True  (T True  x11 x10) (T False x00 x01)
     (True,  True,  False) -> isoTT' $ join $ T True  (T False x10 x11) (T True  x01 x00)
     (True,  True,  True)  -> isoTT' $ join $ T True  (T True  x11 x10) (T True  x01 x00)
 = case (b,c,d) of
     (False, False, False) -> isoTT' $ T False x00 x11
     (False, False, True)  -> isoTT' $ T False x00 x11
     (False, True,  False) -> isoTT' $ T True  x11 x00
     (False, True,  True)  -> isoTT' $ T True  x11 x00
     (True,  False, False) -> isoTT' $ T True  x11 x00
     (True,  False, True)  -> isoTT' $ T True  x11 x00
     (True,  True,  False) -> isoTT' $ T True  x11 x00
     (True,  True,  True)  -> isoTT' $ T True  x11 x00
 = case (b,c,d) of
     (False, False, False) -> T' False x00 x11
     (False, False, True)  -> T' False x00 x11
     (False, True,  False) -> T' True  x00 x11
     (False, True,  True)  -> T' True  x00 x11
     (True,  False, False) -> T' True  x00 x11
     (True,  False, True)  -> T' True  x00 x11
     (True,  True,  False) -> T' True  x00 x11
     (True,  True,  True)  -> T' True  x00 x11
-}
instance Monad Twist' where
  ma >>= k = joinTwist' $ fmap k ma

joinTwist' :: Twist' (Twist' a) -> Twist' a
joinTwist' (T' b (T' c x00 _) (T' _ _ x11)) = T' (b || c) x00 x11

joinTwist'viaIso :: Twist' (Twist' a) -> Twist' a
joinTwist'viaIso = isoTT' . join . isoT'T . fmap isoT'T

enumTwist' :: (Alternative f) => f a -> f (Twist' a)
enumTwist' as = T' <$> (pure True <|> pure False) <*> as <*> as

--------------------------------

-- Nonempty zip(ish)-list, by treating finite list as "converging" sequence.
-- By "converging", I mean, it repeats the same value after finite elements.

data Nez a = Last a | ConsNez a (Nez a)
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

headNezzle :: Nez a -> a
headNezzle (Last a) = a
headNezzle (ConsNez a _) = a

tailNezzle :: Nez a -> Nez a
tailNezzle (Last a) = Last a
tailNezzle (ConsNez _ as) = as

instance Applicative Nez where
  pure = Last
  (<*>) = ap

instance Monad Nez where
  Last a >>= k = k a
  ConsNez a as >>= k =
    ConsNez (headNezzle (k a)) (as >>= tailNezzle . k)

-- Not exhaustive; only up to length 3
enumNezzle :: (Alternative f) => f a -> f (Nez a)
enumNezzle as = s (s one)
  where
    one = Last <$> as
    s n = one <|> (ConsNez <$> as <*> n)

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

instance Applicative Odd where
  pure a = Odd a Nil
  (<*>) = ap

instance Monad Odd where
  ma >>= k = ostep ma
    where
      ostep (Odd x xs) = k x `plusOE` estep xs

      estep Nil = Nil
      estep (Even x xs) = k x `plusOO` ostep xs

-- [x] or [x,y,z]
enumOdd :: Alternative f => f a -> f (Odd a)
enumOdd as = as1 <|> as3
  where
    as0 = pure Nil
    as1 = Odd <$> as <*> as0
    as2 = Even <$> as <*> as1
    as3 = Odd <$> as <*> as2

-- (3n+1)-lengthed list, (4n+1)-lengthed list, ...
-- are also Monads.

newtype List3Np1 a = List3Np1 [a]
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  -- Monad instance inherited from [] keeps invariant.
  deriving (Applicative, Monad) via []

unfoldrList3Np1 :: (s -> Either a (a, a, a, s)) -> s -> List3Np1 a
unfoldrList3Np1 f = List3Np1 . go
  where
    go s = case f s of
      Left a -> [a]
      Right (a0, a1, a2, s') -> a0 : a1 : a2 : go s'

toList3Np1 :: [a] -> Maybe (List3Np1 a)
toList3Np1 as
  | n `rem` 3 == 1 = Just (List3Np1 as)
  | otherwise = Nothing
  where
    n = length as

makeInftyList3Np1 :: (s -> (a, s)) -> s -> List3Np1 a
makeInftyList3Np1 f s = List3Np1 (unfoldr (Just . f) s)
