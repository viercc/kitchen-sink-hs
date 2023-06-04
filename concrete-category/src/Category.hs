{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Category where

import Data.Kind
import Data.Type.Equality

type family Ob (cat :: k -> k -> Type) :: k -> Type

type Category :: (k -> k -> Type) -> Constraint
class (TestEquality (Ob cat)) => Category cat where
  dom :: cat a b -> Ob cat a
  cod :: cat a b -> Ob cat b
  ident :: Ob cat a -> cat a a
  compose :: cat a b -> cat b c -> cat a c

infixr 2 >>>

(>>>) :: (Category hom) => hom a b -> hom b c -> hom a c
(>>>) = compose

infixr 2 <<<

(<<<) :: (Category hom) => hom b c -> hom a b -> hom a c
(<<<) = flip compose

-- * Sample of categories

data Discrete ob a b where
  DiscreteIdent :: ob a -> Discrete ob a a

type instance Ob (Discrete ob) = ob

deriving instance (Show (ob a)) => Show (Discrete ob a b)

deriving instance (Eq (ob a)) => Eq (Discrete ob a b)

deriving instance (Ord (ob a)) => Ord (Discrete ob a b)

instance (TestEquality ob) => Category (Discrete ob) where
  dom (DiscreteIdent a) = a
  cod (DiscreteIdent a) = a
  ident = DiscreteIdent
  compose (DiscreteIdent _) g = g

data Indiscrete ob a b where
  Indiscrete :: ob a -> ob b -> Indiscrete ob a b

type instance Ob (Indiscrete ob) = ob

deriving instance (Show (ob a), Show (ob b)) => Show (Indiscrete ob a b)

deriving instance (Eq (ob a), Eq (ob b)) => Eq (Indiscrete ob a b)

deriving instance (Ord (ob a), Ord (ob b)) => Ord (Indiscrete ob a b)

instance (TestEquality ob) => Category (Indiscrete ob) where
  dom (Indiscrete a _) = a
  cod (Indiscrete _ b) = b
  ident a = Indiscrete a a
  compose (Indiscrete a _) (Indiscrete _ b) = Indiscrete a b