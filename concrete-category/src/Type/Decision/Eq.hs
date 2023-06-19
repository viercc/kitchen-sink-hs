{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE EmptyCase #-}
module Type.Decision.Eq(
    module Type.Decision,

    (:~:)(..),

    Deq(..), (===?),
    deqInner, deqOuter,

    Deq2(..),

    -- | @V1 :: k -> Type@ is a valid type of \"singletons\". Namely,
    --   the empty set of types of kind @k@.
    V1()
) where

import Data.Kind
import Data.Type.Equality
import GHC.Generics(V1())
import Type.Decision

type Deq :: (k -> Type) -> Constraint
-- | Decidable type equality
class Deq f where
    deq :: f a -> f b -> Decision (a :~: b)

(===?) :: Deq f => f a -> f b -> Decision (a :~: b)
(===?) = deq
infix 4 ===?

instance Deq ((:~:) a) where
    deq :: (a :~: b) -> (a :~: c) -> Decision (b :~: c)
    deq Refl Refl = Proved Refl

instance Deq V1 where
    deq x = case x of {}

deqInner :: Decision (a :~: b) -> Decision (f a :~: f b)
deqInner = equivalent (\Refl -> Refl) (\Refl -> Refl)

deqOuter :: Decision (f :~: g) -> Decision (f a :~: g a)
deqOuter = equivalent (\Refl -> Refl) (\Refl -> Refl)

type Deq2 :: (j -> k -> Type) -> Constraint
class Deq2 f where
    deq2 :: f a b -> f a' b' -> Decision (a :~: a', b :~: b')
