{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module DifferenceApplicative where

import Control.Applicative

newtype Diff f a = Diff
  { unDiff :: forall u y z.
    (forall x. (x -> y) -> f x -> z) ->
    (a -> u -> y) -> f u -> z }

instance Functor (Diff f) where
  fmap g x = Diff (\k f -> unDiff x k (f . g))

instance Applicative (Diff f) where
  pure a = Diff (\k f -> k (f a))
  x <*> y = Diff (\k f -> unDiff x (unDiff y k . flip) (\ab u a -> f (ab a) u))

liftDiff :: Applicative f => f a -> Diff f a
liftDiff fa = Diff (\k f fu -> k id (liftA2 f fa fu))

retractDiff :: Applicative f => Diff f a -> f a
retractDiff x = unDiff x fmap const (pure ())

improve :: (forall h. Applicative h => (f a -> h a) -> h a)
        -> (forall g. Applicative g => (f a -> g a) -> g a)
improve interpreter step = retractDiff (interpreter (liftDiff . step))