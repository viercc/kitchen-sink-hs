#!/usr/bin/env cabal
{- cabal:
build-depends: base, recursion-schemes
-}
{-# LANGUAGE TypeFamilies, LambdaCase, DataKinds, DeriveFunctor #-}
module Main where

import Data.Void
import Data.Functor.Foldable
import GHC.TypeLits

data ExprF pass f
  = LitF Int
  | OpF f f
  | ExtF !(XExprF pass)
  deriving (Functor)

type family XExprF (pass :: Nat) :: * where
  XExprF 1 = String
  XExprF 2 = Void

step_OP :: Fix (ExprF 1) -> Fix (ExprF 2)
step_OP = cata f
  where
    f :: ExprF 1 (Fix (ExprF 2)) -> Fix (ExprF 2)
    f = \case
      LitF i  -> Fix (LitF i)
      OpF a b -> Fix (OpF a b)
      ExtF _t -> Fix (ExtF (error "Don't want this here." :: Void))

step1 :: Fix (ExprF 1) -> Fix (ExprF 2)
step1 = hoist $ \case
  LitF i -> LitF i
  OpF a b -> OpF a b
  ExtF t -> LitF (length t)

step2 :: Fix (ExprF 1) -> Maybe (Fix (ExprF 2))
step2 = cata $ \case
  LitF i  -> Just $ Fix (LitF i)
  OpF a b -> fmap Fix $ OpF <$> a <*> b
  ExtF _  -> Nothing

main :: IO ()
main = putStrLn "Compiles"
