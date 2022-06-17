{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
module Data.Functor.Flip1 where

import Control.Applicative
import Control.Monad
import Control.Monad.Free ( MonadFree(..) )
import Data.Kind ( Type )
import Data.Functor.Classes

type Flip1 :: (k1 -> k2 -> Type -> Type) -> k2 -> k1 -> Type -> Type
newtype Flip1 t f g x = Flip1 { unFlip1 :: t g f x }
  deriving stock (Eq, Ord, Show, Read, Traversable)
  deriving (Functor, Foldable, Applicative, Alternative, Monad, MonadPlus,
            MonadFail) via (t g f)
  deriving (Eq1, Ord1, Show1, Read1) via (t g f)

instance (Functor h, MonadFree h (t g f)) => MonadFree h (Flip1 t f g) where
    wrap = Flip1 . wrap . fmap unFlip1