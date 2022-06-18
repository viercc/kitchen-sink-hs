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

module FMonad.State1(State1(..), cisState, transState) where

import Data.Functor.Day
import Data.Functor.Day.Curried
import FMonad

newtype State1 s x a = State1 {
        runState1 :: Curried s (Day s x) a
    }
    deriving Functor

pureState :: x a -> State1 s x a
pureState x = State1 $ unapplied x

joinState :: Functor s => State1 s (State1 s x) a -> State1 s x a
joinState = State1 . ffmap applied . runState1 . ffmap runState1

cisState :: (forall r. s r -> (s r, x a)) -> State1 s x a
cisState f = State1 $ Curried $ \s -> let (s', x) = f s in Day s' x ($)

transState :: (forall r. s r -> (s a, x r)) -> State1 s x a
transState f = State1 $ Curried $ \s -> let (s', x) = f s in Day s' x (flip ($))

instance Functor s => FFunctor (State1 s) where
    ffmap fg (State1 st) = State1 $ ffmap (ffmap fg) st

instance Functor s => FMonad (State1 s) where
    fpure = pureState
    fjoin = joinState
