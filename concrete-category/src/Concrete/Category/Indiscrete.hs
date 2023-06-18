{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
module Concrete.Category.Indiscrete where

import Data.Kind

import Concrete.Span
import Concrete.Category
import Concrete.Decision

type Full :: (j -> Type) -> (k -> Type) -> j -> k -> Type
data Full s t a b = Full (s a) (t b)
    deriving (Show, Eq, Ord)

instance (Deq s, Deq t) => Span s t (Full s t) where
    dom (Full a _) = a
    cod (Full _ b) = b

type Indiscrete s = Full s s

type instance Ob (Full s s) = s

instance (Deq s) => Category (Indiscrete s) where
    ident a = Full a a
    compose (Full a _) (Full _ b) = Full a b