{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Partial.Monad.Free where

import Prelude hiding (id, (.))
import Control.Category (Category (..))
import Partial
import Partial.Functor
import Partial.Monad
import Control.Monad (ap)
import Control.Arrow (Arrow(arr))

-- | The free PMonad.
--
-- (This is completely same to @Control.Monad.Free.Free@ in "free" package and
-- it could have been replaced by that, but it is done anyway to avoid
-- depending on "free".)
data Free f a = Pure a | Free (f (Free f a))
  deriving Functor

instance Functor f => Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance Functor f => Monad (Free f) where
    Pure a >>= k = k a
    Free fma >>= k = Free $ fmap (>>= k) fma

instance PFunctor f => PFunctor (Free f) where
  pmap f = Partial $ \case
    Pure a   -> Pure <$> runPartial f a
    Free fma -> Free <$> runPartial (pmap (pmap f)) fma

instance PFunctor f => PMonad (Free f) where
  ppure = arr pure
  {-
  Equivalent to
    pbind f = arr join . pmap f
  but unfolded and fused the recursion for efficiency
  -}
  pbind f = Partial $ \case
    Pure a -> runPartial f a
    Free fma -> Free <$> runPartial (pmap (pbind f)) fma

hoist :: PFunctor g => (forall a. f a -? g a) -> Free f b -? Free g b
hoist fg = Partial go
  where
    go (Pure a) = Just $ Pure a
    go (Free fma) = Free <$> runPartial (pmap (Partial go) . fg) fma

liftF :: Functor f => f a -> Free f a
liftF fa = Free (Pure <$> fa)

retract :: PMonad f => Free f a -? f a
retract = Partial go
  where
    go (Pure a) = runPartial ppure a
    go (Free fma) = runPartial (pbind (Partial go)) fma