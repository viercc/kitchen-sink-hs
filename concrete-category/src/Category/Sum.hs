{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Category.Sum where

import Category
import Data.Kind (Type)
import Data.Type.Equality (TestEquality (..), (:~:) (..))

type SumOb :: (j -> Type) -> (k -> Type) -> (Either j k -> Type)
data SumOb c0 d0 a where
  Lob :: c0 a -> SumOb c0 d0 ('Left a)
  Rob :: d0 a -> SumOb c0 d0 ('Right a)

instance (TestEquality c0, TestEquality d0) => TestEquality (SumOb c0 d0) where
  testEquality (Lob a) (Lob b) = testEquality a b >>= \Refl -> Just Refl
  testEquality (Rob a) (Rob b) = testEquality a b >>= \Refl -> Just Refl
  testEquality _ _ = Nothing

type Sum ::
  (j -> j -> Type) ->
  (k -> k -> Type) ->
  (Either j k -> Either j k -> Type)
data Sum c d a b where
  Lmor :: c a b -> Sum c d ('Left a) ('Left b)
  Rmor :: d a b -> Sum c d ('Right a) ('Right b)

type instance Ob (Sum c d) = SumOb (Ob c) (Ob d)

instance (Category c, Category d) => Category (Sum c d) where
  dom (Lmor x) = Lob (dom x)
  dom (Rmor x) = Rob (dom x)

  cod (Lmor x) = Lob (cod x)
  cod (Rmor x) = Rob (cod x)

  ident (Lob a) = Lmor (ident a)
  ident (Rob a) = Rmor (ident a)

  compose (Lmor x) (Lmor y) = Lmor (compose x y)
  compose (Rmor x) (Rmor y) = Rmor (compose x y)
