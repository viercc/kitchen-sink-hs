{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
module Concrete.Object.Constrained where

import Data.Kind (Type, Constraint)
import Type.Decision.Eq

type (:=>:) :: (k -> Constraint) -> (k -> Type) -> (k -> Type)
data (:=>:) con s a where
  RestrictedOb :: con a => !(s a) -> (:=>:) con s a

instance (Deq s) => Deq (con :=>: s) where
  deq (RestrictedOb a) (RestrictedOb b) = deq a b