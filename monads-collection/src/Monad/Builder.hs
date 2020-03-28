{-

https://stackoverflow.com/questions/59780866/creating-a-result-piecewise-from-stateful-computation-with-good-ergonomics

-}
{-# LANGUAGE DeriveFunctor, DerivingVia #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
module Monad.Builder(
  Builder(), runBuilder, output,
  ASetter
) where

import Control.Applicative
import Control.Monad.State

import Data.Functor.Identity

newtype Builder s o x = Builder
  { runBuilder' :: s -> o -> (s, o, x) }
  deriving stock Functor
  deriving Applicative via (WrappedMonad (Builder s o))

runBuilder :: (s -> o) -> Builder s o x -> State s (o, x)
runBuilder mkDefaultO (Builder build) =
  state $ \sInitial ->
    let ~(s, o, x) = build sInitial (mkDefaultO s)
    in ((o, x), s)

-- The only allowed operation on @o@ is putting a value through a setter
output :: ASetter o o a a -> a -> Builder s o ()
output l a = Builder $ \s o -> (s, f o, ())
  where f = runIdentity . l (const (Identity a))
{-# INLINEABLE output #-}

type ASetter s t a b = (a -> Identity b) -> s -> Identity t

-- Lazy-for-s, strict-for-o state monad over (s,o)
instance Monad (Builder s o) where
  return x = Builder $ \s o -> (s, o, x)
  {-# INLINEABLE return #-}
  
  ma >>= k = Builder $ \s o ->
    let (s', !o', a) = runBuilder' ma s o
    in runBuilder' (k a) s' o'
  {-# INLINEABLE (>>=) #-}

instance MonadState s (Builder s o) where
  state f = Builder $ \s o ->
    let (a, s') = f s
    in (s', o, a)
  {-# INLINEABLE state #-}
