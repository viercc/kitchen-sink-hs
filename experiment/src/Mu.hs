{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Mu where

import Data.Functor.Compose

type (∘) = Compose

newtype Mu f = Mu (forall a. (f a -> a) -> a)

cata :: forall f a. Functor f => (f a -> a) -> Mu f -> a
cata alg (Mu m) = m alg

roll :: forall f. (Functor f) => f (Mu f) -> Mu f
roll fm = Mu $ \alg -> alg (fmap (cata alg) fm)

unroll :: forall f. (Functor f) => Mu f -> f (Mu f)
unroll = cata (fmap roll)

-- Is this a pair of isomorphisms? How should I prove?
iso1 :: forall f g. (Functor f, Functor g) => Mu (f ∘ g) -> f (Mu (g ∘ f))
iso1 = cata alg
  where
    alg :: Compose f g (f (Mu (g ∘ f))) -> f (Mu (g ∘ f))
    alg = fmap (roll . Compose) . getCompose

iso2 :: forall f g. (Functor f, Functor g) => f (Mu (g ∘ f)) -> Mu (f ∘ g)
iso2 = roll . Compose . fmap iso1
