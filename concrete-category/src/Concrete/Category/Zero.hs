{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Concrete.Category.Zero where

import Data.Kind

import Concrete.Decision
import Concrete.Span
import Concrete.Category

type Zero :: (j -> Type) -> (k -> Type) -> j -> k -> Type
data Zero s t a b
    deriving (Show, Eq, Ord)

instance (Deq s, Deq t) => Span s t (Zero s t) where
    dom z = case z of {}
    cod z = case z of {}

type Zero' = Zero V1 V1

type instance Ob (Zero V1 V1) = V1

instance Category Zero' where
    ident z = case z of {}
    compose z = case z of {}