{-

https://stackoverflow.com/questions/59780866/creating-a-result-piecewise-from-stateful-computation-with-good-ergonomics

-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Monad.Builder
  ( Builder (),
    runBuilder,
    output,
    ASetter,
  )
where

import Control.Monad.State
import Data.Functor.Identity
import Control.Monad (ap)

-- | Lazy-for-s, strict-for-o state monad over (s,o)
newtype Builder s o x = Builder
  {runBuilder' :: s -> o -> (s, o, x)}
  deriving stock (Functor)

runBuilder :: (s -> o) -> Builder s o x -> State s (o, x)
runBuilder mkDefaultO (Builder build) =
  state $ \sInitial ->
    let ~(s, o, x) = build sInitial (mkDefaultO s)
     in ((o, x), s)

-- The only allowed operation on @o@ is putting a value through a setter
output :: ASetter o o a a -> a -> Builder s o ()
output l a = Builder $ \s o -> (s, f o, ())
  where
    f = runIdentity . l (const (Identity a))
{-# INLINEABLE output #-}

type ASetter s t a b = (a -> Identity b) -> s -> Identity t

instance Applicative (Builder s o) where
  pure x = Builder $ \s o -> (s, o, x)
  (<*>) = ap

instance Monad (Builder s o) where
  ma >>= k = Builder $ \s o ->
    let (s', !o', a) = runBuilder' ma s o
     in runBuilder' (k a) s' o'
  {-# INLINEABLE (>>=) #-}

instance MonadState s (Builder s o) where
  state f = Builder $ \s o ->
    let (a, s') = f s
     in (s', o, a)
  {-# INLINEABLE state #-}
