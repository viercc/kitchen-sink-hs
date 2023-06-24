{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Concrete.Object.Constrained where

import Data.Kind (Type, Constraint)
import Type.Decision.Eq
import Concrete.Object

type (:&:) :: (k -> Constraint) -> (k -> Type) -> (k -> Type)
data (:&:) con s a where
  RestrictedOb :: con a => !(s a) -> (:&:) con s a

instance (con a, IsObject s a) => IsObject (con :&: s) a where
  isObject = RestrictedOb isObject

instance (Deq s) => Deq (con :&: s) where
  deq (RestrictedOb a) (RestrictedOb b) = deq a b