{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Concrete.Category.Product where

import Concrete.Decision
import Concrete.Span
import Concrete.Category

import Data.Kind (Type)

type ProductOb :: (j -> Type) -> (k -> Type) -> ((j, k) -> Type)
data ProductOb c0 d0 a where
  Pob :: c0 a -> d0 b -> ProductOb c0 d0 '(a, b)

instance (Deq c0, Deq d0) => Deq (ProductOb c0 d0) where
  deq (Pob a b) (Pob a' b') =
    equivalent (\(Refl,Refl) -> Refl) (\Refl -> (Refl,Refl)) $ dand (a ===? a') (b ===? b')

type Product ::
  (j -> j -> Type) ->
  (k -> k -> Type) ->
  ((j, k) -> (j, k) -> Type)
data Product c d a b where
  Pmor :: c a b -> d a' b' -> Product c d '(a, a') '(b, b')

instance (Span ca cb c, Span da db d) => Span (ProductOb ca da) (ProductOb cb db) (Product c d) where
  dom (Pmor x y) = Pob (dom x) (dom y)
  cod (Pmor x y) = Pob (cod x) (cod y)

type instance Ob (Product c d) = ProductOb (Ob c) (Ob d)

instance (Category c, Category d) => Category (Product c d) where
  ident (Pob a a') = Pmor (ident a) (ident a')
  compose (Pmor x x') (Pmor y y') = Pmor (compose x y) (compose x' y')
