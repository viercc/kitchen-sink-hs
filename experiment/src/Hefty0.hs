{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveFunctor #-}
module Hefty0 where

import GHC.Generics (V1(), (:+:)(..))

-- Inspired by: "Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects"
-- https://dl.acm.org/doi/10.1145/3571255

newtype Hefty0 t = H [t (Hefty0 t)]
    deriving (Semigroup, Monoid) via [t (Hefty0 t)]

deriving stock instance (Show (t (Hefty0 t))) => Show (Hefty0 t)
deriving stock instance (Eq (t (Hefty0 t))) => Eq (Hefty0 t)

singleton :: t (Hefty0 t) -> Hefty0 t
singleton th = H [th]

---- Hefty0 algebras

type Alg t m = t m -> m -> m

cata :: Functor t => m -> Alg t m -> Hefty0 t -> m
cata e alg (H xs) = foldr (alg . fmap (cata e alg)) e xs

zeroAlg :: Alg V1 m
zeroAlg v1 = case v1 of { }

sumAlg :: Alg s m -> Alg t m -> Alg (s :+: t) m
sumAlg alg1 alg2 st m = case st of
    L1 sm -> alg1 sm m
    R1 tm -> alg2 tm m

elaborate :: Functor t => Alg t [c] -> Hefty0 t -> [c]
elaborate = cata []

-- Hefty0 "effects"

newtype Lift c a = Lift c
    deriving (Show, Eq, Functor)

eLift :: (c -> c') -> Alg (Lift c) [c']
eLift inj (Lift c) xs = inj c : xs

type Stop = Lift ()

eStop :: Alg Stop [Maybe c]
eStop = eLift (const Nothing)

data Catch a = Catch a a
    deriving (Show, Eq, Functor)

eCatch :: Alg Catch [Maybe c]
eCatch (Catch xs ys) zs = go xs
  where
    go [] = zs
    go (Just a : xs') = Just a : go xs'
    go (Nothing : _) = ys


-- * Sum of the effects (this time manually done, but can be automated)

type Ins c = Lift c :+: (Stop :+: Catch)

_lift :: c -> Hefty0 (Ins c)
_lift c = singleton (L1 (Lift c))

_stop :: Hefty0 (Ins c)
_stop = singleton (R1 (L1 (Lift ())))

_catch :: Hefty0 (Ins c) -> Hefty0 (Ins c) -> Hefty0 (Ins c)
_catch xs ys = singleton (R1 (R1 (Catch xs ys)))

-- * Interpreting the sum

run :: Monoid m => Hefty0 (Ins m) -> m
run = mconcat . takeWhileJust . elaborate (eLift Just `sumAlg` (eStop `sumAlg` eCatch))
  where
    takeWhileJust :: [Maybe m] -> [m]
    takeWhileJust = foldr (maybe (const []) (:)) []

-- * Example using them all

ex1, ex2, ex3 :: Hefty0 (Ins String)
ex1 = _lift "Hello, " <> _lift "world!"
ex2 = _lift "Hello, " <> _stop <> _lift "world!"
ex3 = _catch ex2 (_lift "and you're caught!")