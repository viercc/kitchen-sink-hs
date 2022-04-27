{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
-- | Basically a copy of 'Data.Functor.Day.Curried' module from
--   "kan-extensions", but uses Yoneda'd form to get rid of
--   @'Functor' f@ requirement from @Functor (Curried f g)@ instance.
module Functor.Day.Curried where

import Data.Functor.Day
import Control.Applicative

import FFunctor

newtype Curried f g a = Curried
  { runCurried :: forall r s. f r -> (r -> a -> s) -> g s }
  deriving stock Functor

toCurried :: (forall x. Day f g x -> h x) -> g a -> Curried f h a
toCurried fg_h g = Curried (\f op -> fg_h (Day f g op))

fromCurried :: (forall x. f x -> Curried g h x) -> Day g f b -> h b
fromCurried f_g_h (Day g f op) = runCurried (f_g_h f) g op

applied :: Day f (Curried f g) a -> g a
applied = fromCurried id

unapplied :: g a -> Curried f (Day f g) a
unapplied = toCurried id

liftCurried :: Applicative f => f a -> Curried f f a
liftCurried f2 = Curried (\f1 op -> liftA2 op f1 f2)

lowerCurried :: Applicative f => Curried f g a -> g a
lowerCurried fg = runCurried fg (pure id) ($)

rap :: Curried f g (a -> b) -> Curried g h a -> Curried f h b
rap fg gh = Curried $ \f op -> runCurried gh (runCurried fg f (\r ab -> op r . ab)) ($)

instance (Functor g, g ~ h) => Applicative (Curried g h) where
    pure a = Curried $ \f op -> (`op` a) <$> f
    (<*>) = rap

instance FFunctor (Curried g) where
    ffmap tr gh = Curried $ \g op -> tr (runCurried gh g op)

