{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

module Concrete.Category.Sum where

import Concrete.Decision
import Concrete.Span
import Concrete.Category

import Data.Kind (Type)

type SumOb :: (j -> Type) -> (k -> Type) -> (Either j k -> Type)
data SumOb c0 d0 a where
  Lob :: c0 a -> SumOb c0 d0 ('Left a)
  Rob :: d0 a -> SumOb c0 d0 ('Right a)

instance (Deq c0, Deq d0) => Deq (SumOb c0 d0) where
  deq (Lob a) (Lob b) = deqInner (a ===? b)
  deq (Rob a) (Rob b) = deqInner (a ===? b)
  deq (Lob _) (Rob _) = Disproved (\case)
  deq (Rob _) (Lob _) = Disproved (\case)

type Sum ::
  (j -> j -> Type) ->
  (k -> k -> Type) ->
  (Either j k -> Either j k -> Type)
data Sum c d a b where
  Lmor :: c a b -> Sum c d ('Left a) ('Left b)
  Rmor :: d a b -> Sum c d ('Right a) ('Right b)

instance (Span ca cb c, Span da db d) => Span (SumOb ca da) (SumOb cb db) (Sum c d) where
  dom (Lmor x) = Lob (dom x)
  dom (Rmor x) = Rob (dom x)

  cod (Lmor x) = Lob (cod x)
  cod (Rmor x) = Rob (cod x)

type instance Ob (Sum c d) = SumOb (Ob c) (Ob d)

instance (Category c, Category d) => Category (Sum c d) where
  ident (Lob a) = Lmor (ident a)
  ident (Rob a) = Rmor (ident a)

  compose (Lmor x) (Lmor y) = Lmor (compose x y)
  compose (Rmor x) (Rmor y) = Rmor (compose x y)
