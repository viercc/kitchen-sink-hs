{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Object.Sum where

import Data.Kind (Type)
import Type.Decision.Eq
import Concrete.Object

type (:+:) :: (j -> Type) -> (k -> Type) -> (Either j k -> Type)
data (:+:) c0 d0 a where
  Lob :: c0 a -> (c0 :+: d0) ('Left a)
  Rob :: d0 a -> (c0 :+: d0) ('Right a)

instance (IsObject c0 a) => IsObject (c0 :+: d0) ('Left a) where
  isObject = Lob isObject

instance (IsObject d0 b) => IsObject (c0 :+: d0) ('Right b) where
  isObject = Rob isObject

instance (Deq c0, Deq d0) => Deq (c0 :+: d0) where
  deq (Lob a) (Lob b) = deqInner (a ===? b)
  deq (Rob a) (Rob b) = deqInner (a ===? b)
  deq (Lob _) (Rob _) = Disproved (\case)
  deq (Rob _) (Lob _) = Disproved (\case)
