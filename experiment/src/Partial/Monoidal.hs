{-# LANGUAGE TypeOperators #-}

module Partial.Monoidal where

import Data.These
import Partial
import Partial.Functor
import Prelude hiding (id, (.))

class (PFunctor f) => PMonoidal f where
  pmult :: These (f a) (f b) -? f (These a b)
