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

instance (Span c, Span d) => Span (Product c d) where
  type Dom (Product c d) = Dom c :*: Dom d
  type Cod (Product c d) = Cod c :*: Cod d
  dom (Pmor x y) = Pob (dom x) (dom y)
  cod (Pmor x y) = Pob (cod x) (cod y)

instance (Category c, Category d) => Category (Product c d) where
  ident (Pob a a') = Pmor (ident a) (ident a')
  compose (Pmor x x') (Pmor y y') = Pmor (compose x y) (compose x' y')
