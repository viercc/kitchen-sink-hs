{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Category.Trivial where

import Category
import Data.Kind (Type)
import Data.Type.Equality (TestEquality (..), (:~:) (..))

type One :: () -> () -> Type
data One a b where
  One :: One '() '()

type instance Ob One = ((:~:) '())

deriving instance Show (One a b)

deriving instance Eq (One a b)

deriving instance Ord (One a b)

instance Category One where
  dom One = Refl
  cod One = Refl
  ident Refl = One
  compose One r = r

data ZeroOb a
  deriving (Show, Eq, Ord)

instance TestEquality ZeroOb where
  testEquality a = case a of {}

data Zero a b
  deriving (Show, Eq, Ord)

type instance Ob Zero = ZeroOb

instance Category Zero where
  dom x = case x of {}
  cod x = case x of {}
  ident a = case a of {}
  compose x = case x of {}
