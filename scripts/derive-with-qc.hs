#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}
{-# LANGUAGE RankNTypes, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}

import Data.Kind (Type)

data State
  = A
  | B

data Thing :: (State -> State -> Type -> Type) -> Type where
  IntThing :: f a b Int -> f b c Int -> Thing f
  DoubleThing :: f a b Double -> f b c Double -> Thing f

deriving instance (forall i j a . Show a => Show (f i j a)) => Show (Thing f)

newtype SampleF (a :: State) (b :: State) x =
  SampleF x
  deriving (Show)

sampleThing1, sampleThing2 :: Thing SampleF
sampleThing1 = IntThing (SampleF 1) (SampleF 2)
sampleThing2 = DoubleThing (SampleF 1.5) (SampleF 2.5)

main :: IO ()
main = print [sampleThing1, sampleThing2]

