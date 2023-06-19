{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Category.Product where

import Data.Kind (Type)

import Concrete.Span
import Concrete.Category
import Concrete.Object.Product

type Product ::
  (j -> j' -> Type) ->
  (k -> k' -> Type) ->
  ((j, k) -> (j', k') -> Type)
data Product c d a b where
  Pmor :: c a b -> d a' b' -> Product c d '(a, a') '(b, b')

instance (Span ca cb c, Span da db d) => Span (ca :*: da) (cb :*: db) (Product c d) where
  dom (Pmor x y) = Pob (dom x) (dom y)
  cod (Pmor x y) = Pob (cod x) (cod y)

type instance Ob (Product c d) = Ob c :*: Ob d

instance (Category c, Category d) => Category (Product c d) where
  ident (Pob a a') = Pmor (ident a) (ident a')
  compose (Pmor x x') (Pmor y y') = Pmor (compose x y) (compose x' y')
