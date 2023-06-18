{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Concrete.Category.Discrete where

import Data.Kind

import Concrete.Span
import Concrete.Category
import Concrete.Decision

type Diag :: (k -> Type) -> k -> k -> Type
data Diag s a b where
    Diag :: s a -> Diag s a a

type Discrete = Diag

deriving instance Show (s b) => Show (Diag s b c)
deriving instance Eq (s b) => Eq (Diag s b c)
deriving instance Ord (s b) => Ord (Diag s b c)

instance (Deq s) => Span s s (Diag s) where
    dom (Diag a) = a
    cod (Diag a) = a

instance (Deq s) => Function s s (Diag s) where
    isFunction (Diag _) (Diag _) = Refl
    apply a = Some (Diag a)

type instance Ob (Diag s) = s

instance (Deq s) => Category (Diag s) where
    ident = Diag
    compose (Diag _) r = r