{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
module Partial.Monad where

import Prelude hiding (id, (.))

import Partial
import Partial.Functor

class PFunctor m => PMonad m where
  ppure :: a -? m a
  pbind :: (a -? m b) -> m a -? m b
  pjoin :: m (m a) -? m a
