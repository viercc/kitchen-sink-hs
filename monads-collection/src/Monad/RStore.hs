{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Monad.RStore where

import Control.Monad
import Control.Comonad
import Control.Comonad.Store

newtype R w a = R { runR :: forall r. (a -> w r) -> r }
  deriving Functor

instance Comonad w => Applicative (R w) where
  pure x = R $ \k -> extract (k x)
  (<*>) = ap

instance Comonad w => Monad (R w) where
  rw >>= k = R $ \cont -> runR rw (\x -> runR (k x) (duplicate . cont))

newtype Q s a = Q { runQ :: (a -> s) -> (a, s) }
  deriving Functor

instance Applicative (Q s) where
  pure x = Q $ \f -> (x, f x)
  (<*>) = ap

instance Monad (Q s) where
  qx >>= k = joinQ (fmap k qx)

joinQ :: Q s (Q s a) -> Q s a
joinQ qqx = Q $ \f ->
  let (qx, s) = runQ qqx (\qx' -> snd (runQ qx' f))
      x = fst (runQ qx f)
  in (x, s)

fromRStore :: R (Store s) a -> Q s a
fromRStore rx = Q $ \f -> runR rx (\x -> store (x, ) (f x))

toRStore :: Q s a -> R (Store s) a
toRStore qx = R $ \k ->
  let (x,s) = runQ qx (pos . k)
  in peek s (k x)

