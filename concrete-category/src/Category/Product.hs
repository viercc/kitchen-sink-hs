{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Category.Product where

import Category
import Data.Kind (Type)
import Data.Type.Equality (TestEquality (..), (:~:) (..))

type ProductOb :: (j -> Type) -> (k -> Type) -> ((j, k) -> Type)
data ProductOb c0 d0 a where
  Pob :: c0 a -> d0 b -> ProductOb c0 d0 '(a, b)

instance (TestEquality c0, TestEquality d0) => TestEquality (ProductOb c0 d0) where
  testEquality (Pob a b) (Pob a' b') =
    testEquality a a' >>= \Refl ->
      testEquality b b' >>= \Refl ->
        Just Refl

type Product ::
  (j -> j -> Type) ->
  (k -> k -> Type) ->
  ((j, k) -> (j, k) -> Type)
data Product c d a b where
  Pmor :: c a b -> d a' b' -> Product c d '(a, a') '(b, b')

type instance Ob (Product c d) = ProductOb (Ob c) (Ob d)

instance (Category c, Category d) => Category (Product c d) where
  dom (Pmor x y) = Pob (dom x) (dom y)
  cod (Pmor x y) = Pob (cod x) (cod y)
  ident (Pob a a') = Pmor (ident a) (ident a')
  compose (Pmor x x') (Pmor y y') = Pmor (compose x y) (compose x' y')
