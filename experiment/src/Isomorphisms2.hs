-- Overkilling a cute li'l exercise
--   https://www.reddit.com/r/haskell/comments/v0mfkl/cute_lil_exercise/
{-# LANGUAGE UnicodeSyntax, TypeOperators, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

-- (this time without ImpredicativeTypes, but I'm not sure it's better or not)
module Isomorphisms2(goal, to, from) where

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
eitherToMaybe = Iso (either Just (const Nothing)) (maybe (Right ()) Left)

unitFunction :: Iso x (() -> x)
unitFunction = Iso const ($ ())

-- * Facts about "forall"'d types

-- | @Lim f@ is an alias for @forall x. f x@
newtype Lim f = MkLim { runLim :: forall x. f x }

-- | 'Data.Functor.Identity' but terse
newtype I x = I x

-- | 'Data.Functor.Const' but terse
newtype K x y = K x

-- | Function with parameters
newtype (:->:) f g a = Arr1 { runArr1 :: f a -> g a }
infixr 4 :->:
infixl 8 `runArr1`

-- | > Iso (forall x. (c -> x) -> f x) (Yoneda f c)
wrapYoneda :: Iso (Lim ((->) c :->: f)) (Yoneda f c)
wrapYoneda = coercionIso

-- | The "Yoneda Lemma".
yonedaLemma :: Functor f => Iso (Yoneda f c) (f c)
yonedaLemma = Iso lowerYoneda liftYoneda

-- | > Iso (∀x. a -> t x) (a -> ∀x. t x)
flipForall :: forall a t. Iso (Lim (K a :->: t)) (a -> Lim t)
flipForall = Iso to' from'
  where
    to' f a = MkLim (runArr1 (runLim f) (K a))
    from' g = MkLim (Arr1 (\(K a) -> runLim (g a)))

pointwiseIso :: forall t u. (∀x. Iso (t x) (u x)) -> Iso (Lim t) (Lim u)
pointwiseIso e = Iso to' from'
  where
    to' ty = MkLim (_to e (runLim ty))
    from' uz = MkLim (_from e (runLim uz))

-- * Complete the proof!

-- | Our goal is to make an isomorphism between the types below
type F a b = Lim (K a :->: I :->: Either b)
type F' a b = a -> Maybe b

wrapF :: (forall x. a -> x -> Either b x) -> F a b
wrapF f = MkLim (Arr1 $ \(K a) -> Arr1 $ \(I x) -> f a x)

unwrapF :: F a b -> (forall x. a -> x -> Either b x)
unwrapF f a x = runLim f `runArr1` K a `runArr1` I x

goal' :: Iso (Lim (I :->: Either b)) (Maybe b)
goal' = pointwiseIso toYonedaForm >>> wrapYoneda >>> yonedaLemma >>> eitherToMaybe
  where
    toYonedaForm :: forall f x. Iso ((I :->: f) x) (((->) () :->: f) x)
    toYonedaForm = coerce (preIso @x @(() -> x) @(f x) unitFunction)

goal :: Iso (F a b) (F' a b)
goal = flipForall >>> postIso goal'

to :: (forall x. a -> x -> Either b x) -> (a -> Maybe b)
to x = _to goal (wrapF x)

from :: (a -> Maybe b) -> (forall x. a -> x -> Either b x)
from y = unwrapF (_from goal y)

-- Examples

-- testT == testT'
testT :: Bool -> x -> Either String x
testT False _ = Left "False!"
testT True  x = Right x

testT'' :: Bool -> x -> Either String x
testT'' = from (to testT)

-- testU == testU'
testU :: Bool -> Maybe String
testU False = Just "False!!!"
testU True  = Nothing

testU'' :: Bool -> Maybe String
testU'' = to (from testU)
