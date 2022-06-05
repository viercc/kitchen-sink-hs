-- Overkilling a cute li'l exercise
--   https://www.reddit.com/r/haskell/comments/v0mfkl/cute_lil_exercise/
{-# LANGUAGE UnicodeSyntax, ScopedTypeVariables, ImpredicativeTypes #-}
module Isomorphisms(goal) where

import Prelude hiding (id, (.))
import Control.Category

import Data.Coerce

import Data.Functor.Yoneda

-- | Type of isomorphisms
data Iso a b = Iso { _to :: a -> b, _from :: b -> a }

instance Category Iso where
    id = Iso id id
    Iso bc cb . Iso ab ba = Iso (bc . ab) (ba . cb)

-- * Some facts about isomorphisms
fmapIso :: Functor f => Iso a b -> Iso (f a) (f b)
fmapIso (Iso ab ba) = Iso (fmap ab) (fmap ba)

preIso :: Iso a b -> Iso (a -> r) (b -> r)
preIso (Iso ab ba) = Iso (. ba) (. ab)

postIso :: Iso a b -> Iso (s -> a) (s -> b)
postIso = fmapIso

-- | Coercion is an isomorphism
coercionIso :: Coercible a b => Iso a b
coercionIso = Iso coerce coerce

-- * Some known isomorphisms
eitherToMaybe :: Iso (Either b ()) (Maybe b)
eitherToMaybe = Iso to from
  where
    to (Left b) = Just b
    to (Right ()) = Nothing
    from (Just b) = Left b
    from Nothing = Right ()

unitFunction :: Iso x (() -> x)
unitFunction = Iso to from
  where
    to = const
    from f = f ()

-- * Facts about "forall"'d types

-- The "Yoneda Lemma".
wrapYoneda :: Iso (∀r. (c -> r) -> f r) (Yoneda f c)
wrapYoneda = coercionIso

yonedaLemma :: Functor f => Iso (Yoneda f c) (f c)
yonedaLemma = Iso lowerYoneda liftYoneda

-- It's generally true that
--
-- > ∀(T :: Type -> Type). Iso (∀x. a -> T x) (a -> ∀x. T x)
--   
-- but GHC doesn't have a first-class type function.
--
-- This fact is used only once, so I'll write it for one specialized @T b@.
flipForall :: Iso (∀x. a -> T b x) (a -> ∀x. T b x)
flipForall = Iso to from
  where
    to :: ∀a b. (∀x. a -> T b x) -> (a -> ∀x. T b x)
    to f a = f a
    from :: ∀a b. (a -> ∀x. T b x) -> (∀x. a -> T b x)
    from g a = g a

-- It's generally true that
--
-- >  ∀(T, U :: Type -> Type). (∀x. Iso (T x) (U x)) -> (Iso (∀y. T y) (∀z. U z))
--
-- but GHC doesn't have a first-class type function.
-- 
-- This fact is used only once, so I'll write it for one specialized for each T and U.
pointwiseIso :: ∀b. (∀x. Iso (T b x) (U b x))
                -> Iso (∀y. T b y) (∀z. U b z)
pointwiseIso e = Iso to from
    where
    to :: (∀y. T b y) -> (∀z. U b z)
    to ty = _to e ty
    from :: (∀z. U b z) -> (∀y. T b y)
    from uz = _from e uz

type T b x = x -> Either b x
type U b x = (() -> x) -> Either b x

-- * Complete the proof!

-- | Our goal is to make an isomorphism of the type below
type Goal a b = Iso (∀x. a -> x -> Either b x) (a -> Maybe b)

-- | ... but it's more convenient to get rid of @a@ from the goal.
type Goal' b = Iso (∀x. x -> Either b x) (Maybe b)

-- | Goal can be shown using Goal'.
goalFromGoal' :: Goal' b -> Goal a b
goalFromGoal' assumedGoal' = flipForall >>> postIso assumedGoal'

goal' :: Goal' b
goal' = toYonedaForm >>> wrapYoneda >>> yonedaLemma >>> eitherToMaybe
  where
    toYonedaForm :: Iso (∀x. x -> Either b x) (∀x. (() -> x) -> Either b x)
    toYonedaForm = pointwiseIso (preIso unitFunction)

goal :: Goal a b
goal = goalFromGoal' goal'

-- Examples

-- testT == testT''
testT :: Bool -> x -> Either String x
testT False _ = Left "False!"
testT True  x = Right x

testT' :: Bool -> Maybe String
testT' = let to = _to goal in to testT

testT'' :: Bool -> x -> Either String x
testT'' = let from = _from goal in from testT'

-- testU == testU''
testU :: Bool -> Maybe String
testU False = Just "False!!!"
testU True  = Nothing

testU' :: Bool -> x -> Either String x
testU' = let from = _from goal in from testU

testU'' :: Bool -> Maybe String
testU'' = let to = _to goal in to testU'
