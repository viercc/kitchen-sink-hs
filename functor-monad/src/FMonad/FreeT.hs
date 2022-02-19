{-# LANGUAGE
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
module FMonad.FreeT(
    module FMonad,
    FreeT'(..)
) where

import Control.Monad (MonadPlus)
import Control.Applicative (Alternative)
import Data.Functor.Classes

import Control.Monad.Trans.Free

import Data.Bifunctor
import FMonad

-- | FreeT' is argument-flipped 'FreeT'
newtype FreeT' m f b = FreeT' { unFreeT' :: FreeT f m b }
    deriving (Applicative, Alternative, Monad, MonadPlus,
              Foldable, Eq1, Ord1, Show1, Read1)
        via (FreeT f m)
    deriving (Show, Read, Eq, Ord)
        via (FreeT f m b)

instance (Functor m, Functor f) => Functor (FreeT' m f) where
    fmap f (FreeT' mx) = FreeT' (fmapFreeT_ f mx)

instance (Traversable f, Traversable m) => Traversable (FreeT' m f) where
    traverse f (FreeT' mx) = FreeT' <$> traverseFreeT f mx

traverseFreeT :: (Traversable f, Traversable m, Applicative g)
  => (a -> g b) -> FreeT f m a -> g (FreeT f m b)
traverseFreeT f = go
  where
    go (FreeT x) = FreeT <$> traverse goF x
    goF (Pure a)   = Pure <$> f a
    goF (Free fmx) = Free <$> traverse go fmx

instance Functor m => FFunctor (FreeT' m) where
    ffmap f = FreeT' . transFreeT_ f . unFreeT'

instance Monad m => FMonad (FreeT' m) where
    fpure :: forall g. Functor g => g ~> FreeT' m g
    fpure = FreeT' . inl
    
    fjoin :: forall g. Functor g => FreeT' m (FreeT' m g) ~> FreeT' m g
    fjoin = FreeT' . fjoin_ . transFreeT_ unFreeT' . unFreeT'
      where
        fjoin_ :: FreeT (FreeT g m) m ~> FreeT g m
        fjoin_ = eitherFreeT id inr

-- Sadly, Functor (FreeT m f) uses liftM instead of fmap,
-- meaning (Monad m, Functor f) => Functor (FreeT f m).
-- Maybe that was for backward compatibility,
-- but I want (Functor m, Functor f) => ...
fmapFreeT_ :: (Functor f, Functor m) => (a -> b) -> FreeT f m a -> FreeT f m b
fmapFreeT_ f = let go = FreeT . fmap (bimap f go) . runFreeT in go

ffmapFreeF :: forall f g a. (f ~> g) -> FreeF f a ~> FreeF g a
ffmapFreeF _  (Pure a)  = Pure a
ffmapFreeF fg (Free fb) = Free (fg fb)

transFreeT_ :: forall f g m. (Functor g, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
transFreeT_ fg =
  let go = FreeT . fmap (fmap go . ffmapFreeF fg) . runFreeT in go

inr :: Functor m => m ~> FreeT f m
inr = FreeT . fmap Pure

inl :: (Functor f, Monad m) => f ~> FreeT f m
inl = FreeT . return . Free . fmap return

eitherFreeT :: Monad n => (f ~> n) -> (m ~> n) -> (FreeT f m ~> n)
eitherFreeT nt1 nt2 = go
  where
    go ma =
      do v <- nt2 (runFreeT ma)
         case v of
           Pure a  -> return a
           Free fm -> nt1 fm >>= go
