{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Category.WithOb where

import Category
import qualified Control.Category as Base
import Data.Type.Equality (TestEquality (..))

data With ob cat a b = With !(ob a) !(ob b) !(cat a b)
  deriving (Show, Eq, Ord)

type instance Ob (With ob cat) = ob

instance (TestEquality ob, Base.Category cat) => Category (With ob cat) where
  dom (With a _ _) = a
  cod (With _ b _) = b
  ident a = With a a Base.id
  compose (With a _ x) (With _ c y) = With a c (x Base.>>> y)
