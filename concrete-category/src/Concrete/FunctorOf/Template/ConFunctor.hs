{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Concrete.FunctorOf.Template.ConFunctor where

import Data.Kind

import Concrete.Span
import Concrete.Category
import Concrete.FunctorOf
import Data.Proxy

type Con :: (j -> j -> Type) -> (k -> k -> Type) -> (j -> k) -> n -> Constraint
class (Category c, Category d) => Con c d f name | f name -> c d where
    fmapImpl :: proxy name -> c a b -> d (f a) (f b)
    
    obmapImpl :: proxy name -> Ob c a -> Ob d (f a)
    obmapImpl n a = dom (fmapImpl n (ident a))


type Wrap :: (j -> Type) -> (k -> Type) -> (j -> k) -> n -> j -> k -> Type
data Wrap s t f name a b where
    Mk :: s a -> t (f a) -> Wrap s t f name a (f a)

instance Span (Wrap s t f name) where
    type Dom (Wrap s t f name) = s
    type Cod (Wrap s t f name) = t
    dom (Mk a _) = a
    cod (Mk _ fa) = fa

instance (Con c d f name, Ob c ~ s, Ob d ~ t) => Function (Wrap s t f name) where
    isFunction (Mk _ _) (Mk _ _) = Refl
    apply a = Some (Mk a (obmapImpl (Proxy @name) a))

instance (Category c, Category d, Ob c ~ s, Ob d ~ t, Con c d f name) => FunctorOf c d (Wrap s t f name) where
    fmapAt (Mk _ _) (Mk _ _) = fmapImpl (Proxy @name)