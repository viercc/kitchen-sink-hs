{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Concrete.FunctorOf.Template.IdOnObjectFunctor where

import Data.Kind

import Concrete.Span
import Concrete.Category
import Concrete.FunctorOf
import Concrete.Category.Discrete (Diag(..))
import Data.Proxy

type IdOnObject :: (k -> k -> Type) -> (k -> k -> Type) -> name -> Constraint
class (Category c, Category d) => IdOnObject c d n | n c -> d, n d -> c where
    fmapImpl :: proxy n -> c a b -> d a b

-- * Newtype wrapper

type Wrap :: (k -> Type) -> name -> k -> k -> Type
newtype Wrap s n a b = Mk (Diag s a b)

deriving newtype instance Span (Wrap s n)
deriving newtype instance Function (Wrap s n)

instance (Category c, Category d, Ob c ~ s, Ob d ~ s, IdOnObject c d n) => FunctorOf c d (Wrap s n) where
    fmapAt (Mk (Diag _)) (Mk (Diag _)) = fmapImpl (Proxy @n)