{-# LANGUAGE
  QuantifiedConstraints,
  DerivingVia,
  DerivingStrategies,
  DeriveTraversable,
  StandaloneDeriving,
  
  RankNTypes,
  ScopedTypeVariables,
  
  InstanceSigs,
  TypeOperators,
  TupleSections
#-}

module FMonad.State1 where

import Data.Functor.Day
import Data.Functor.Day.Curried
import FMonad

newtype State1 s x a = State1 {
        runState1 :: Curried s (Day s x) a
    }
    deriving Functor

instance Functor s => FFunctor (State1 s) where
    ffmap fg (State1 st) = State1 $ ffmap (ffmap fg) st
instance Functor s => FMonad (State1 s) where
    fpure fx = State1 $ Curried $ \s -> Day s fx id
    fjoin = State1 . ffmap applied . runState1 . ffmap runState1
