{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{- |

==== Record of failure!

I tried to make an "exotic" (i.e., not isomorphic to the standard)
continuation monad using the "Monad.RStore" module.

@Monad.RStore@ establishes a monad isomorphism between
@G s ~ Codensity ((,) s)@ and @Q s@, whose underlying functor
is isomorphic to @S s :*: C s@,
where @S s@ and @C s@ are the (standard) selection and continuation
monads, respectively.

The idea is that @S s :*: C s@ can have another @Monad@ instance:
there is the product of monads @Product (S s) (C s)@. By transferring this monad
via the isomorphism connecting @G s@ and @S s :*: C s@, we get a non-standard @Monad@
instance on the same underlying functor as @G s@. Let's call this new monad @G' s@. 

The underlying functor of @G' s@ is *almost* a continuation monad.

@
newtype G' s a   = G' {
    runG' :: forall r. (a -> (r, s)) -> (r, s)
  }
newtype Cont r a = Cont {
    runCont :: (a -> r) -> r
  }
@

If we could "monomorphize" the quantified @r@ type variable
in the definition of @G'@ while retaining the monad structure of @G'@,
we would get a new monad @G'' s a@, which is functor-isomorphic to @Cont (R, s) a@ for some @R@,
but not monad-isomorphic to @Cont (R, s) a@.

But it didn't go well! The culprit is the naturality I implicitly assumed.
A value of @G' s a ~ forall r. (a -> (r, s)) -> (r, s)@
is assumed to be /natural in @r@/, which means this function can't touch the value of
type @r@. This naturality is important when proving that the @Monad@ instance for @G' s@ is lawful.
Once we "monomorphize" it to any non-trivial @R@,
a value of the new type can now touch @R@, which increases the set of possible behaviors in a way
that causes the monad implementation to fail the monad laws.

-}

module Monad.ExoticCont where

import Control.Monad ( ap )
import Data.Coerce (coerce, Coercible)
import Data.Functor.Product (Product (..))

import Monad.RStore
import Data.Bifunctor (first)

newtype Q' s a = Q' { runQ' :: (a -> s) -> (a, s) }
  deriving Functor

instance Applicative (Q' s) where
  pure :: forall a. a -> Q' s a
  pure x = Q' $ \k -> (x, k x)

  (<*>) = ap

instance Monad (Q' s) where
  ma >>= f = pairQ' (splitQ' ma >>= splitQ' . f)

splitQ' :: Q' s ~> Product (S s) (C s)
splitQ' (Q' f) = Pair (S (fst . f)) (C (snd . f))

pairQ' :: Product (S s) (C s) ~> Q' s
pairQ' (Pair (S sa) (C ca)) = Q' $ \k -> (sa k, ca k)

newtype G' s a = G' { runG' :: forall r. (a -> (r, s)) -> (r, s) }
  deriving Functor

coerce1 :: forall f g x. Coercible (f x) (g x) => f x -> g x
coerce1 = coerce

fromG' :: forall s. G' s ~> Q' s
-- fromG' = coerce1 . fromG . coerce1 @(G' s) @(G s)
fromG' gx = Q' $ \f -> runG' gx (\x -> (x, f x))

toG' :: forall s. Q' s ~> G' s
-- toG' = coerce1 @(G s) @(G' s) . toG . coerce1
toG' qx = G' $ \k -> first (fst . k) (runQ' qx (snd . k))

instance Applicative (G' s) where
  pure a = G' ($ a)
  {-
  pure a
   = toG' (pure a)
   = toG' (Q' $ \f -> (a, f a))
   = G' $ \k -> first (fst . k) ((\f -> (a, f a)) (snd . k))
   = G' $ \k -> first (fst . k) (a, snd (k a))
   = G' $ \k -> (fst (k a), snd (k a))
   = G' $ \k -> k a
  -}

  (<*>) = ap

instance Monad (G' s) where
  ma >>= k = toG' (fromG' ma >>= fromG' . k)
{-
ma >>= k
 = toG' (fromG' ma >>= fromG' . k)
 = toG' (pairQ' (splitQ' (fromG' ma) >>= splitQ' . fromG' . k))
 = sc2g (g2sc ma >>= g2sc . k)
 = sc2g (Pair sa ca >>= \a -> Pair (ks a) (kc a))
  where
    qa = \f -> runG' ga (\x -> (x, f x))
    sa = S $ \f -> fst (qa f)
    ca = C $ \f -> snd (qa f)

    kq = \a f -> runG' (k a) (\x -> (x, f x))
    ks = \a -> S $ \f -> fst (kq a f)
    kc = \a -> C $ \f -> snd (kq a f)
 = sc2g (Pair (sa >>= ks) (ca >>= kc))
 = sc2g (Pair sb cb)
  where
    sb = sa >>= ks
     = S $ \f ->
        let g = \a -> f (runS (ks a) f)
        in runS (ks (runS sa g)) f
     = S $ \f ->
        let g a = f (fst (kq a f))
        in  fst (kq (runS sa g) f)
     = S $ \f ->
        let g a = f (fst (kq a f))
        in  fst (kq (fst (qa g)) f)
    cb = ca >>= kc
     = C $ \f -> runC ca $ \a -> runC (kc a) f
     = C $ \f -> (\f' -> snd (qa f')) $ \a -> snd (kq a f)
     = C $ \f ->
        let g a = snd (kq a f)
        in snd (qa g)
  = G' $ \h ->
     let h1 = fst . h
         h2 = snd . h
     in (h1 (sb h2), cb h2)
  = G' $ \h ->
     let h1 = fst . h
         h2 = snd . h
         r = h1 (sa h2)
          = let g a = h2 (fst (kq a h2))
            in h1 (fst (kq (fst (qa g)) h2))
         s =
          let g a = snd (kq a h2)
          in snd (qa g)
     in (r, s)
  = G' $ \h ->
     let h1 = fst . h
         h2 = snd . h
         g' a = kq a h2
         r = h1 (sa h2)
          = let g a = h2 (fst (kq a h2))
            in h1 (fst (kq (fst (qa g)) h2))
         s =
          let g a = snd (kq a h2)
          in snd (qa g)a
     in (r, s)

sc2g = toG' . pairQ' :: Product (S s) (C s) ~> G' s
sc2g (Pair (S sa) (C ca))
  = toG' (pairQ' (S sa) (C ca))
  = toG' $ Q' $ \k -> (sa k, ca k)
  = G' $ \k -> first (fst . k) ((\f -> (sa f, ca f)) (snd . k))
  = G' $ \k -> first (fst . k) (sa (snd . k), ca (snd . k))
  = G' $ \k -> ((fst . k) (sa (snd . k)), ca (snd . k))
  = G' $ \k ->
      let k1 = fst . k
          k2 = snd . k
      in (k1 (sa k2), ca k2)

g2sc = splitQ' . fromG' :: G' s ~> Product (S s) (C s)
g2sc ga = Pair sa ca
 where
   qa = runQ' (fromG' ga)
    = \f -> runG' ga (\x -> (x, f x))
   sa = S . (fst .) . runQ' . fromG' $ ga  
    = S . (fst .) $ qa
    = S $ \f -> fst (qa f)
   ca = C $ \f -> snd (qa f)
-}

sc2g :: Product (S s) (C s) ~> G' s
sc2g (Pair (S sa) (C ca))
  = G' $ \k ->
      let k1 = fst . k
          k2 = snd . k
      in (k1 (sa k2), ca k2)

bindG'_ev :: forall s a b. G' s a -> (a -> G' s b) -> forall r. (b -> (r, s)) -> (r, s)
bindG'_ev ga k h = runG' (sc2g (Pair (sa >>= ks) (ca >>= kc))) h
  where
    qa :: (a -> s) -> (a, s)
    qa = \f -> runG' ga (\x -> (x, f x))

    sa = S $ \f -> fst (qa f)
    ca = C $ \f -> snd (qa f)

    kq :: a -> (b -> s) -> (b, s)
    kq = \a f -> runG' (k a) (\x -> (x, f x))
    ks = \a -> S $ \f -> fst (kq a f)
    kc = \a -> C $ \f -> snd (kq a f)

bindG'_ev2 :: forall s a b r. G' s a -> (a -> G' s b) -> (b -> (r, s)) -> (r, s)
bindG'_ev2 ga k h = (r', s')
  where
    qa :: (a -> s) -> (a, s)
    qa = \f -> runG' ga (\x -> (x, f x))

    h2 = snd . h

    g' :: a -> (s, s)
    g' a = runG' (k a) (\x -> (h2 x, h2 x))

    g'1 :: a -> s
    g'1 a = fst (g' a)

    g'2 :: a -> s
    g'2 a = snd (g' a)

    gg :: a -> (r, s)
    gg a = runG' (k a) h

    r' = fst (gg (fst (qa g'1)))
    s' = snd (qa g'2)

newtype G'' s a = G'' { runG'' :: (a -> (s, s)) -> (s, s) }
  deriving Functor

instance Applicative (G'' s) where
  pure a = G'' $ \f -> f a
  (<*>) = ap

instance Monad (G'' s) where
  (>>=) = bindG''

bindG'' :: forall s a b. G'' s a -> (a -> G'' s b) -> G'' s b
bindG'' ga k = G'' $ \h -> 
  let h2 = snd . h

      k1 :: a -> s
      k1 a = fst $ runG'' (k a) (\x -> (h2 x, h2 x))

      k2 :: a -> s
      k2 a = snd $ runG'' (k a) (\x -> (h2 x, h2 x))

      k3 :: a -> s
      k3 a = fst $ runG'' (k a) h

      qa :: (a -> s) -> (s, s)
      qa = \f -> runG'' ga (\x -> (k3 x, f x))
  in (fst (qa k1), snd (qa k2))

{-

[Left Unit]
pure a >>= k
 = G'' $ \h -> let
    h2 = snd . h

    k1 :: a -> s
    k1 a = fst $ runG'' (k a) (\x -> (h2 x, h2 x))

    k2 :: a -> s
    k2 a = snd $ runG'' (k a) (\x -> (h2 x, h2 x))

    k3 :: a -> s
    k3 a = fst $ runG'' (k a) h

    qa :: (a -> s) -> (s, s)
    qa = \f -> runG'' (pure a) (\x -> (k3 x, f x))
      = (k3 a, f a)
  in (fst (qa k1), snd (qa k2))
 = G'' $ \h -> let
    h2 = snd . h

    k2 :: a -> s
    k2 a = snd $ runG'' (k a) (\x -> (h2 x, h2 x))

    k3 :: a -> s
    k3 a = fst $ runG'' (k a) h

  in (k3 a, k2 a)

THIS CAN'T BE EQUAL TO (k a)!!

k a
  = G'' $ \h -> let
    k3 :: a -> s
    k3 a = fst $ runG'' (k a) h

    k4 :: a -> s
    k4 a = snd $ runG'' (k a) h

  in (k3 a, k4 a)


[Right Unit]
ga >>= pure
 = G'' $ \h -> let
    h1 = fst . h
    h2 = snd . h

    k1 :: a -> s
    k1 a = fst $ runG'' (pure a) (\x -> (h2 x, h2 x))
     = fst (h2 a, h2 a)
     = h2 a

    k2 :: a -> s
    k2 a = snd $ runG'' (pure a) (\x -> (h2 x, h2 x))
     = snd (h2 a, h2 a)
     = h2 a

    k3 :: a -> s
    k3 a = fst $ runG'' (pure a) h
     = fst (h a)
     = h1 a

    qa :: (a -> s) -> (s, s)
    qa = \f -> runG'' ga (\x -> (k3 x, f x))
  
  in (fst (qa k1), snd (qa k2))

 = G'' $ \h -> let
    h1 = fst . h
    h2 = snd . h

    qa :: (a -> s) -> (s, s)
    qa = \f -> runG'' ga (\x -> (h1 x, f x))
  
  in (fst (qa h2), snd (qa h2))

 = G'' $ \h -> let
    qa :: (a -> s) -> (s, s)
    qa = \f -> runG'' ga (\x -> ((fst . h) x, f x))
  in qa (snd . h)

 = G'' $ \h -> runG'' ga h
 = ga

-}