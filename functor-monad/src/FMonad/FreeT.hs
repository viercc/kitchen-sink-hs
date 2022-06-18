{-# LANGUAGE
  PatternSynonyms,

  QuantifiedConstraints,
  DerivingVia,
  DerivingStrategies,
  DeriveTraversable,
  StandaloneDeriving,
  
  PolyKinds,
  
  RankNTypes,
  ScopedTypeVariables,
  
  InstanceSigs,
  TypeOperators,
  TupleSections
#-}
{-# LANGUAGE FlexibleInstances #-}
module FMonad.FreeT(
    module FMonad,
    FreeT(..),
    type FreeT',
    pattern FreeT',
    Flip1(..)
) where

import Control.Monad (MonadPlus)
import Control.Applicative (Alternative)
import Data.Functor.Classes

import Control.Monad.Trans.Free hiding (FreeT())
import qualified Control.Monad.Trans.Free as Original
import Control.Monad.Trans.Free.Extra

import FMonad
import Data.Functor.Flip1

-- | Redefine FreeT so that some instances don't require 'Monad' instead of 'Functor'
newtype FreeT f m b = WrapFreeT { unwrapFreeT :: Original.FreeT f m b }
    deriving (Applicative, Alternative, Monad, MonadPlus,
              Foldable, Eq1, Ord1, Show1, Read1)
        via (Original.FreeT f m)
    deriving (Show, Read, Eq, Ord)
        via (Original.FreeT f m b)

type FreeT' = Flip1 FreeT

pattern FreeT' :: Original.FreeT f m a -> FreeT' m f a
pattern FreeT'{ unFreeT' } = Flip1 (WrapFreeT unFreeT' )

instance (Functor m, Functor f) => Functor (FreeT m f) where
    fmap f = WrapFreeT . fmapFreeT_ f . unwrapFreeT

instance (Traversable f, Traversable m) => Traversable (FreeT f m) where
    traverse f (WrapFreeT mx) = WrapFreeT <$> traverseFreeT_ f mx

instance Functor f => FFunctor (FreeT f) where
    ffmap f = WrapFreeT . hoistFreeT f . unwrapFreeT

instance Functor f => FMonad (FreeT f) where
    fpure = WrapFreeT . inr
    fjoin = WrapFreeT . fconcatFreeT_ . hoistFreeT unwrapFreeT . unwrapFreeT

instance Functor m => FFunctor (FreeT' m) where
    ffmap f = FreeT' . transFreeT_ f . unFreeT'

instance Monad m => FMonad (FreeT' m) where
    fpure :: forall g. Functor g => g ~> FreeT' m g
    fpure = FreeT' . inl
    
    fjoin :: forall g. Functor g => FreeT' m (FreeT' m g) ~> FreeT' m g
    fjoin = FreeT' . fjoin_ . transFreeT_ unFreeT' . unFreeT'
      where
        fjoin_ :: Original.FreeT (Original.FreeT g m) m ~> Original.FreeT g m
        fjoin_ = eitherFreeT_ id inr
