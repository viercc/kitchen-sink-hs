{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Concrete.Category.One where

import Data.Kind

import Concrete.Span
import Concrete.Category

type One :: k -> k -> k -> Type
data One a b c where
    One :: One a a a

deriving instance Show (One a b c)
deriving instance Eq (One a b c)
deriving instance Ord (One a b c)

instance Span (One a) where
    type Dom (One a) = ((:~:) a)
    type Cod (One a) = ((:~:) a)
    dom One = Refl
    cod One = Refl

instance Function (One a) where
    isFunction One One = Refl
    apply Refl = Some One

instance Category (One a) where
    ident Refl = One
    compose One r = r