{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
module Monad.Free where

import           Control.Monad

-----------------------------------------
-- The Free monad
-----------------------------------------
data Free f a = Pure a
              | Free (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap k (Pure a)  = Pure (k a)
  fmap k (Free fa) = Free (fmap (fmap k) fa)

instance Functor f => Applicative (Free f) where
  pure    = Pure
  Pure a  <*> b = fmap a b
  Free fa <*> b = Free (fmap (<*> b) fa)

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a  >>= k = k a
  Free fa >>= k = Free (fmap (>>= k) fa)

-- Converts to another monad m by giving natural transformation
foldFree :: Monad m => (forall x. f x -> m x) -> Free f a -> m a
foldFree _ (Pure a)  = return a
foldFree p (Free fa) = p fa >>= foldFree p

-- Lift natural transformation @forall x. f x -> g x@ to
-- natural transformation of Free: @forall a. Free f a -> Free g a@
hoistFree :: Functor g => (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree _ (Pure a)  = Pure a
hoistFree p (Free fa) = Free (fmap (hoistFree p) (p fa))

-- hoistFree id = id
-- foldFree id . hoistFree p = foldFree p

-----------------------------------------
-- Typeclass for free monads
-----------------------------------------
class Monad m => MonadFree f m | m -> f where
  {-# MINIMAL wrap | liftFree #-}

  -- Add an layer of functor
  wrap :: Functor f => f (m a) -> m a
  wrap = join . liftFree
  {-# INLINE wrap #-}

  -- Lift functor value to monad value
  liftFree :: Functor f => f a -> m a
  liftFree = wrap . fmap return
  {-# INLINE liftFree #-}

instance Functor f => MonadFree f (Free f) where
  wrap = Free

-----------------------------------------
-- The Free monad, Church-encoded
-----------------------------------------
newtype F f a = F { runF :: forall r. (a -> r) -> (f r -> r) -> r }

instance Functor (F f) where
  fmap f (F m) = F $ \ret fk -> m (ret . f) fk

{-
fmap id (F m)
  = F $ \ret fk -> m (ret . id) fk
  = F $ \ret fk -> m ret fk
  = F m

(fmap f . fmap g) (F m)
  = F $ \ret1 fk -> (\ret2 fk -> m (ret2 . g) fk) (ret1 . f) fk
  = F $ \ret1 fk -> m ((ret1 . f) . g) fk
  = F $ \ret fk -> m (ret . (f . g)) fk
  = fmap (f . g) (F m)
-}

instance Applicative (F f) where
  pure a = F $ \ret _ -> ret a
  (<*>) = ap

instance Monad (F f) where
  return = pure
  (F ma) >>= f = F $ \ret fk -> ma (\a -> runF (f a) ret fk) fk

instance Functor f => MonadFree f (F f) where
  liftFree fa = F $ \ret fk -> fk (fmap ret fa)
  {-# INLINE liftFree #-}

-- F version of foldFree
foldF :: Monad m => (forall x. f x -> m x) -> F f a -> m a
foldF h (F m) = m return (join . h)

-- F version of hoistFree
hoistF :: Functor g => (forall x. f x -> g x) -> F f a -> F g a
hoistF h (F m) = F $ \ret fk -> m ret (fk . h)

