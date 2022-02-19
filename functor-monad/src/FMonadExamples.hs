{-# LANGUAGE
  StandaloneKindSignatures,
  DerivingVia,
  DerivingStrategies,
  DeriveFunctor,
  StandaloneDeriving,
  RankNTypes,
  ExistentialQuantification,
  ScopedTypeVariables,
  InstanceSigs,
  TypeOperators,
  TupleSections,
  QuantifiedConstraints
#-}
{-

FMonadList on various FMonad:
(Note that `FMonad mm` doesn't imply `Monad (mm f)` or
whatever, but `FMonadList mm` is a `Monad`!)

-}
module FMonadExamples where

import FMonad
-- import ListTVia

{-

1. Free

   FMonadList Free a
    ~ Free (a,) ()
    ~ [a]

2. ReaderT e

   FMonadList (ReaderT e) a
    ~ ReaderT e (a,) ()
    ~ e -> (a,())
    ~ e -> a

3. (Extending 2.) Compose f g


   FMonadList (Compose m) a
     ~ Compose m (a,) ()
     ~ m (a,())
     ~ m a

4. FMonad MaybeT

   MaybeT (MaybeT m) a === m (Maybe (Maybe a))
        |                         |
        v fjoin                   v fmap join
     MaybeT m a        === m (Maybe a)
   
   FMonadList MaybeT a
    ~ (a, Maybe ())
    ~ (a, Bool) by {False <-> Nothing, True <-> Just ()}
    ~ Writer All a

5. (Extending 4.) FlipCompose f g

   FMonadList (FlipCompose m) a
     ~ FlipCompose m (a,) ()
     ~ (a, m ())
     ~ (a, Ap m)
     ~ Writer (Ap m) a

6. Maybe' f = I :+: f
   
   FMonadList Maybe' a
    ~ Maybe' (a,) ()
    ~ Either () (a,())
    ~ Maybe a
-}

data Maybe' f a = Nothing' a | Just' (f a)
  deriving Functor

instance FFunctor Maybe' where
  ffmap _  (Nothing' a) = Nothing' a
  ffmap fg (Just' fa)   = Just' (fg fa)

instance FMonad Maybe' where
  fpure = Just'
  fjoin (Nothing' a)         = Nothing' a
  fjoin (Just' (Nothing' a)) = Nothing' a
  fjoin (Just' (Just' fa))   = Just' fa

-- Another functor related to Day
newtype (:->:) f g x = ExpDay (forall a b. (x -> a -> b) -> f a -> g b)

deriving instance Functor (f :->: g)

instance FFunctor ((:->:) f) where
    ffmap gh (ExpDay e) = ExpDay $ \xa_b fa -> gh (e xa_b fa)

evDay :: Day f (f :->: g) ~> g
evDay (Day ab_x fa (ExpDay e)) = e (flip ab_x) fa

{-

8. State'

   FMonadList (State' s) x
    ~ State' s (x,) ()
    ~ (s :->: Day s (x,)) ()
    ~ forall a b. (() -> a -> b) -> s a -> Day s (x,) b
    ~ forall a b. (a -> b) -> s a -> Day s (x,) b
    ~ forall a b. (a -> b) -> s a -> ∃c d. (c -> d -> b, s c, (x,d))
    ~ forall a b. (a -> b) -> s a -> ∃c. (c -> b, s c, x)
    ~ forall a b. (a -> b) -> s a -> (CoYoneda s b, x)
    ~ forall a. s a -> (forall b. (a -> b) -> (CoYoneda s b, x))
    ~ forall a. s a -> (CoYoneda s a, x)
    (If s is a Functor)
    ~ forall a. s a -> (s a, x)
    ~ forall a. State (s a) x

-}

newtype State' s f x = State' { runState' :: (s :->: Day s f) x }
  deriving Functor

instance FFunctor (State' s) where
    ffmap fg (State' st) = State' $ ffmap (ffmap fg) st
instance FMonad (State' s) where
    fpure fx = State' $ ExpDay $ \xa_b sa -> Day (flip xa_b) sa fx
    fjoin = State' . ffmap evDay . runState' . ffmap runState'
