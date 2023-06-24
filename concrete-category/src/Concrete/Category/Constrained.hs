{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
module Concrete.Category.Constrained where

import Data.Kind
import Concrete.Span
import Concrete.Category
import Concrete.Object.Constrained

type Restrict :: (k -> Constraint) -> (k -> k -> Type) -> (k -> k -> Type)
data Restrict con c a b where
    Restricted :: (con a, con b) => c a b -> Restrict con c a b

instance Span c => Span (Restrict con c) where
    type Dom (Restrict con c) = con :&: Dom c
    type Cod (Restrict con c) = con :&: Cod c

    dom (Restricted x) = RestrictedOb (dom x)
    cod (Restricted x) = RestrictedOb (cod x)

instance Category c => Category (Restrict con c) where
    ident (RestrictedOb a) = Restricted (ident a)
    compose (Restricted x) (Restricted y) = Restricted (compose x y)