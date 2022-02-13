{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
module PartialMonad where

import Prelude hiding (id, (.))
import Control.Monad (ap)
import Control.Category
import Control.Arrow

import GHC.Generics((:+:)(..))

newtype Partial a b = Partial {
    runPartial :: a -> Maybe b
  }
  deriving (Category, Arrow, ArrowChoice) via (Kleisli Maybe)

type (-?) = Partial
infixr 1 -?

newtype Pt f a = Pt (Maybe (f a))

runPt :: Pt f a -? f a
runPt = Partial $ \(Pt pfa) -> pfa

class PFunctor f where
  pmap :: (a -? b) -> f a -? f b

instance PFunctor f => Functor (Pt f) where
  fmap f = Pt . runPartial (pmap (arr f) . runPt)

class PFunctor m => PMonad m where
  ppure :: a -? m a
  pbind :: (a -? m b) -> m a -? m b
  pjoin :: m (m a) -? m a

instance PMonad m => Applicative (Pt m) where
  pure = return
  (<*>) = ap

instance PMonad m => Monad (Pt m) where
  return = Pt . runPartial ppure
  (>>=) = bind_
    where
      bind_ pma k = join_ $ fmap k pma
      join_ = Pt . runPartial (pjoin . pmap runPt . runPt)

newtype Traversed t a = WrapTraversable (t a)
    deriving stock (Eq, Ord, Show, Read)
    deriving newtype (Functor, Foldable, Applicative, Monad)

instance Traversable t => Traversable (Traversed t) where
  traverse f (WrapTraversable ta) = WrapTraversable <$> traverse f ta

instance Traversable t => PFunctor (Traversed t) where
  pmap = Partial . traverse . runPartial

{-
-- Only when 
--    traverse f . pure = fmap pure . f
--    traverse f . join = fmap join . traverse (traverse f)
instance (Traversable t, Monad t) => PMonad (Traversed t) where
  ppure = arr pure
  pjoin = arr join
-}

-- Sum of arrows
para :: ArrowChoice p => p (f a) (f b) -> p (g a) (g b) -> p ((f :+: g) a) ((f :+: g) b)
para pf pg = arr fromE . (pf +++ pg) . arr toE
  where
    toE (L1 fa) = Left fa
    toE (R1 ga) = Right ga

    fromE = either L1 R1

instance (Traversable f, PFunctor g) => PFunctor (f :+: g) where
  pmap f = (Partial . traverse . runPartial $ f) `para` pmap f
