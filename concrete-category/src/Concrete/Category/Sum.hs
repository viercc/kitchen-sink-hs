{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Category.Sum(Sum(..), (:+:)(..)) where

import Data.Kind (Type)

import Concrete.Object.Sum
import Concrete.Span
import Concrete.Category

-- | Sum of two categories.
--
-- >>> :kind Sum
-- Sum :: (j -> j' -> *)
--        -> (k -> k' -> *) -> Either j k -> Either j' k' -> *
-- >>> :kind! Dom (Sum c d)
-- Dom (Sum c d) :: Either j k -> *
-- = Dom c :+: Dom d
-- >>> :kind! Cod (Sum c d)
-- Cod (Sum c d) :: Either j' k' -> *
-- = Cod c :+: Cod d
type Sum ::
  (j -> j' -> Type) ->
  (k -> k' -> Type) ->
  (Either j k -> Either j' k' -> Type)
data Sum c d a b where
  Lmor :: c a b -> Sum c d ('Left a) ('Left b)
  Rmor :: d a b -> Sum c d ('Right a) ('Right b)

instance (Span c, Span d) => Span (Sum c d) where
  type Dom (Sum c d) = Dom c :+: Dom d
  type Cod (Sum c d) = Cod c :+: Cod d
  dom (Lmor x) = Lob (dom x)
  dom (Rmor x) = Rob (dom x)

  cod (Lmor x) = Lob (cod x)
  cod (Rmor x) = Rob (cod x)

instance (Function c, Function d) => Function (Sum c d) where
  isFunction (Lmor ab) (Lmor ab') = case isFunction ab ab' of Refl -> Refl
  isFunction (Rmor ab) (Rmor ab') = case isFunction ab ab' of Refl -> Refl

  apply (Lob a) = case apply a of
    Some cab -> Some (Lmor cab)
  apply (Rob a) = case apply a of
    Some dab -> Some (Rmor dab)

instance (Category c, Category d) => Category (Sum c d) where
  ident (Lob a) = Lmor (ident a)
  ident (Rob a) = Rmor (ident a)

  compose (Lmor x) (Lmor y) = Lmor (compose x y)
  compose (Rmor x) (Rmor y) = Rmor (compose x y)
