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

type Diag :: (k -> Type) -> k -> k -> Type
data Diag s a b where
    Diag :: s a -> Diag s a a

type Discrete = Diag

deriving instance Show (s b) => Show (Diag s b c)
deriving instance Eq (s b) => Eq (Diag s b c)
deriving instance Ord (s b) => Ord (Diag s b c)

instance Span (Diag s) where
    type Dom (Diag s) = s
    type Cod (Diag s) = s
    dom (Diag a) = a
    cod (Diag a) = a

instance Function (Diag s) where
    isFunction (Diag _) (Diag _) = Refl
    apply a = Some (Diag a)

instance Category (Diag s) where
    ident = Diag
    compose (Diag _) r = r