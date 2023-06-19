{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Category.Sum where

import Data.Kind (Type)

import Concrete.Object.Sum
import Concrete.Span
import Concrete.Category

type Sum ::
  (j -> j' -> Type) ->
  (k -> k' -> Type) ->
  (Either j k -> Either j' k' -> Type)
data Sum c d a b where
  Lmor :: c a b -> Sum c d ('Left a) ('Left b)
  Rmor :: d a b -> Sum c d ('Right a) ('Right b)

instance (Span ca cb c, Span da db d) => Span (ca :+: da) (cb :+: db) (Sum c d) where
  dom (Lmor x) = Lob (dom x)
  dom (Rmor x) = Rob (dom x)

  cod (Lmor x) = Lob (cod x)
  cod (Rmor x) = Rob (cod x)

type instance Ob (Sum c d) = Ob c :+: Ob d

instance (Category c, Category d) => Category (Sum c d) where
  ident (Lob a) = Lmor (ident a)
  ident (Rob a) = Rmor (ident a)

  compose (Lmor x) (Lmor y) = Lmor (compose x y)
  compose (Rmor x) (Rmor y) = Rmor (compose x y)
