{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Object.Product where

import Data.Kind (Type)
import Type.Decision.Eq
import Concrete.Object

type (:*:) :: (j -> Type) -> (k -> Type) -> ((j, k) -> Type)
data (:*:) c0 d0 a where
  Pob :: c0 a -> d0 b -> (c0 :*: d0) '(a, b)

instance (IsObject c0 a, IsObject d0 b) => IsObject (c0 :*: d0) '(a,b) where
  isObject = Pob isObject isObject

instance (Deq c0, Deq d0) => Deq (c0 :*: d0) where
  deq (Pob a b) (Pob a' b') =
    equivalent (\(Refl,Refl) -> Refl) (\Refl -> (Refl,Refl)) $ dand (a ===? a') (b ===? b')
