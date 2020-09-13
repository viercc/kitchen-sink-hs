module Poifree where

import Data.Bifunctor
import Control.Monad

import Data.These

newtype Poifree f a = Poifree { runPoifree :: These a (f (Poifree f a)) }

instance Functor f => Functor (Poifree f) where
    fmap f = let go = Poifree . bimap f (fmap go) . runPoifree
             in go

instance Functor f => Applicative (Poifree f) where
    pure = Poifree . This
    (<*>) = ap

instance Functor f => Monad (Poifree f) where
    return = pure
    ma >>= k =
        Poifree .
        merge . bimap (runPoifree . k) (fmap (>>= k)) .
        runPoifree $ ma
      where
        merge :: These (These a b) b -> These a b
        merge (This ab) = ab
        merge (That b) = That b
        merge (These ab b) = second (const b) ab