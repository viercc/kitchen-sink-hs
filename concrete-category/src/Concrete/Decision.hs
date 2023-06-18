{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE EmptyCase #-}
module Concrete.Decision
  ( Not,
    Decision (..),
    dand,
    dor,
    dnot,
    equivalent,

    Deq(..), (===?),
    deqInner, deqOuter,
    Deq2(..),

    -- | @V1 :: k -> Type@ is a valid type of \"singletons\". Namely,
    --   the empty set of types of kind @k@.
    V1()
  )
where

import Data.Type.Equality
import Data.Void
import Data.Kind
import GHC.Generics (V1())

type Not p = p -> Void

-- | Either p or not p is proved
data Decision p = Proved p | Disproved (Not p)

dand :: Decision p -> Decision q -> Decision (p, q)
dand (Proved p) (Proved q) = Proved (p, q)
dand _ (Disproved notq) = Disproved (notq . snd)
dand (Disproved notp) _ = Disproved (notp . fst)

dor :: Decision p -> Decision q -> Decision (Either p q)
dor (Proved p) _ = Proved (Left p)
dor _ (Proved q) = Proved (Right q)
dor (Disproved notp) (Disproved notq) = Disproved (either notp notq)

dnot :: Decision p -> Decision (Not p)
dnot (Proved p) = Disproved ($ p)
dnot (Disproved p) = Proved p

equivalent :: (p -> q) -> (q -> p) -> Decision p -> Decision q
equivalent to from isP = case isP of
  Proved p -> Proved (to p)
  Disproved notP -> Disproved (notP . from)

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
