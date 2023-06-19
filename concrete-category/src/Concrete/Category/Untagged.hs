{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Concrete.Category.Untagged where

import Data.Kind
import qualified Control.Category as Std
import Data.Proxy

import Concrete.Span
import Concrete.Category

-- | Wraps a type with an instance of 'Std.Category' (which is the one in the standard library)
--   to give it an 'Category' instance. The new instance uses 'Proxy' as the tag with no data.
type Untagged :: (j -> k -> Type) -> (j -> k -> Type)
newtype Untagged p a b = Untagged { getUntagged :: p a b }
   deriving (Eq, Ord, Show)
   deriving newtype (Functor, Applicative, Monad, Std.Category)

instance Span Proxy Proxy (Untagged p) where
    dom _ = Proxy
    cod _ = Proxy

type instance Ob (Untagged p) = Proxy

instance Std.Category p => Category (Untagged p) where
    ident _ = Untagged Std.id
    compose (Untagged x) (Untagged y) = Untagged (x Std.>>> y)
