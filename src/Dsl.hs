{-# LANGUAGE
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
module Dsl where

import Control.Monad.State

newtype Dsl r a = Dsl { runDsl :: (a -> r) -> r }
  deriving (Functor)

instance Applicative (Dsl r) where
  pure = return
  (<*>) = ap
instance Monad (Dsl r) where
  return a = Dsl ($ a)
  ma >>= f = Dsl $ \k ->
    runDsl ma (\a -> runDsl (f a) k)

instance MonadState s (Dsl (s -> r)) where
  state f = Dsl $ \k s ->
    let (a,s') = f s in k a s'

instance MonadIO (Dsl (IO r)) where
  liftIO io = Dsl (io >>=)

instance MonadIO (Dsl r) => MonadIO (Dsl (s -> r)) where
  liftIO io = Dsl $ \k s -> runDsl (liftIO io) (\a -> k a s)
