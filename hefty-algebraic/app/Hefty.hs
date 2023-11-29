{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Hefty(
    Hefty(..),
    send,

    Alg, cata,

    Lift(..), eLift,
    Handle(..), eHandle,
    (:++:)(..), (|++|),

    inl, inr,

    Effs, runEffs,
    lift', withHandler
) where

import Control.Monad ( join, ap, (>=>) )
import Control.Monad.Trans.Free (FreeT())

import qualified Control.Monad.Trans.Free as Free

data Hefty h a where
    Pure :: a -> Hefty h a
    Impure :: h (Hefty h) a -> (a -> Hefty h b) -> Hefty h b

send :: h (Hefty h) a -> Hefty h a
send hh = Impure hh Pure

type (~>) f g = forall a. f a -> g a

class (forall f. Functor f => Functor (h f)) => HFunctor h where
    hmap :: (Functor f, Functor g) => (f ~> g) -> h f ~> h g

instance HFunctor h => Functor (Hefty h) where
    fmap f (Pure a) = Pure (f a)
    fmap f (Impure ha k) = Impure ha (fmap f . k)

instance HFunctor h => Applicative (Hefty h) where
    pure = Pure
    (<*>) = ap

instance HFunctor h => Monad (Hefty h) where
    Pure a >>= k = k a
    Impure ha k >>= l = Impure ha (k >=> l)

--------

newtype Lift m f a = Lift (m a)
    deriving Functor

instance Functor m => HFunctor (Lift m) where
    hmap _ (Lift ma) = Lift ma

data Handle f a where
    WithHandler :: forall sig f a. (Functor sig) => (forall x. sig x -> f (Either x a)) -> FreeT sig f a -> Handle f a

deriving instance Functor f => Functor (Handle f)

instance HFunctor Handle where
    hmap fg (WithHandler handler body) = WithHandler (fg . handler) (Free.hoistFreeT fg body)

data (:++:) h j f p = L2 (h f p) | R2 (j f p)
    deriving Functor

infixl 4 :++:

instance (HFunctor h, HFunctor j) => HFunctor (h :++: j) where
    hmap fg (L2 h) = L2 (hmap fg h)
    hmap fg (R2 j) = R2 (hmap fg j)

----

type Alg h f = forall a. h f (f a) -> f a

cata :: (HFunctor h, Functor f) => (forall a. a -> f a) -> Alg h f -> Hefty h b -> f b
cata gen _alg (Pure a) = gen a
cata gen alg  (Impure h k) = alg (cata gen alg . k <$> hmap (cata gen alg) h)

eLift :: Monad m => Alg (Lift m) m
eLift (Lift mma) = join mma

eHandle :: forall m a. Monad m => Handle m (m a) -> m a
eHandle (WithHandler @sig handler body) = go body
  where
    go :: FreeT sig m (m a) -> m a
    go (Free.FreeT mfma) = mfma >>= \case
        Free.Pure ma -> ma
        Free.Free sig -> handler sig >>= either go id

(|++|) :: Alg h1 f -> Alg h2 f -> Alg (h1 :++: h2) f
alg1 |++| alg2 = \case
    L2 h1 -> alg1 h1
    R2 h2 -> alg2 h2

infixl 4 |++|

-- * Utilities

inl :: (Functor f, Monad m) => f ~> FreeT f m
inl = Free.liftF

inr :: (Functor m) => m ~> FreeT f m
inr ma = Free.FreeT (Free.Pure <$> ma)

-- * Lift + Handle

type Effs m = Hefty (Lift m :++: Handle)

lift' :: Functor m => m a -> Effs m a
lift' = send . L2 . Lift

withHandler :: (Functor m, Functor sig) => (forall x. sig x -> Effs m (Either x a)) -> FreeT sig (Effs m) a -> Effs m a
withHandler handler body = send (R2 (WithHandler handler body))

runEffs :: Monad m => Effs m a -> m a
runEffs = cata pure (eLift |++| eHandle)
