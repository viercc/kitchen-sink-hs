{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
module Monad.RStore where

import Data.Bifunctor (first)

import Control.Monad
import Control.Comonad
import Control.Comonad.Store

type (~>) f g = forall x. f x -> g x

-- * R

-- | @R w@ is 'Monad' for every 'Comonad' @w@
newtype R w a = R { runR :: forall r. (a -> w r) -> r }
  deriving Functor

pureR :: Comonad w => a -> R w a
pureR x = R $ \k -> extract (k x)

joinR :: Comonad w => R w (R w a) -> R w a
joinR rrx = R $ \cont -> runR rrx $ \rx -> runR rx (duplicate . cont)

instance Comonad w => Applicative (R w) where
  pure = pureR
  (<*>) = ap

instance Comonad w => Monad (R w) where
  ra >>= k = joinR $ fmap k ra

-- * G

-- | @G s ~ Codensity ((,) s)@
newtype G s a = G { runG :: forall r. (a -> (r,s)) -> (r,s) }
    deriving Functor

g2r :: G s ~> R (Store s)
g2r g = R $ \cont -> unwrap $ runG g (runStore . cont)

r2g :: R (Store s) ~> G s
r2g r = G $ \cont -> runR r (wrap . cont)

unwrap :: (s -> r, s) -> r
unwrap (f, s) = f s

wrap :: (r,s) -> Store s (r,s)
wrap (r,s) = store (r, ) s

wrap' :: (r, s) -> (s -> (r, s), s)
wrap' = runStore . wrap
-- wrap' = first (,)

{- * Proof of the isomorphism-ness of (g2r, r2g) pair

r2g (g2r g)
 = G $ \cont -> runR (g2r g) (wrap . cont)
runG (r2g (g2r g)) cont
 = runR (g2r g) (wrap . cont)
 = unwrap $ runG g (runStore . wrap . cont)
 = unwrap $ runG g (wrap' . cont)
 = unwrap $ runG g (first (,) . cont)
      -- free theorem on (runG g) ...
      --   first p . runG g = runG g . (first p .)
 = unwrap . first (,) $ runG g cont
 = (\(r,s) -> (r,s)) $ runG g cont
 = runG g cont

runR (g2r (r2g r)) cont
 = unwrap $ runG (r2g r) (runStore . cont)
 = unwrap $ runR r (wrap . runStore . cont)
       -- free theorem on (runR r) ...
       --   p . runR r = runR r . (fmap p .)
 = runR r (fmap unwrap . wrap . runStore . cont)
 = runR r (ret . cont)
    where
      ret = fmap unwrap . wrap . runStore
      ret (runStore -> (f,s)) = fmap unwrap (wrap (f,s))
       = fmap unwrap (store (f,) s)
       = store (unwrap . (f,)) s
       = store (\s' -> unwrap (f,s')) s
       = store (\s' -> f s') s
       = store f s
      ret = id
 = runR r cont

-}


pureG, pureG' :: a -> G s a
pureG x = G $ \cont -> cont x
pureG' = r2g . pureR

joinG, joinG' :: G s (G s a) -> G s a
joinG ggx = G $ \cont -> runG ggx $ \gx -> runG gx cont
joinG' = r2g . joinR . fmap g2r . g2r

{- * The isomorphism r2g is a monad morphism

  (therefore the two are isomorphic /as monads/)

  [pureG = pureG']

  pureG' x = r2g (pureR x)
  = G $ \cont -> runR (pureR x) (wrap . cont)
  = G $ \cont -> extract (wrap (cont x))
  = G $ \cont -> (\(r,s) -> extract (store (r,) s)) $ cont x
  = G $ \cont -> (\(r,s) -> (r,s)) $ cont x
  = G $ \cont -> cont x
  = pureG x

  [joinG = joinG']

  joinG' ggx = r2g (joinR (g2r . fmap g2r $ ggx))
  = G $ \cont -> runR (joinR (fmap g2r . g2r $ ggx)) (wrap . cont)
  = G $ \cont ->
      runR (fmap g2r . g2r $ ggx) $ \rx -> runR rx (duplicate . wrap . cont)
  = G $ \cont ->
      runR (g2r ggx) $ \gx ->
        runR (g2r gx) (duplicate . wrap . cont)
  = G $ \cont ->
      unwrap $ runG ggx $ \gx ->
        runStore $ runR (g2r gx) (duplicate . wrap . cont)
  = G $ \cont ->
      unwrap $ runG ggx $ \gx ->
        runStore $ unwrap $ runG gx (runStore . duplicate . wrap . cont)
    {
      (runStore . duplicate . wrap) (r,s)
        = runStore . duplicate $ store (r,) s
        = runStore $ store (store (r,)) s
        = (store (r,), s)
      runStore . duplicate . wrap = first (\r -> store (r,))
    }

  = G $ \cont ->
      unwrap $ runG ggx $ \gx ->
        runStore . unwrap $ runG gx (first (\r -> store (r,)) . cont)

  = G $ \cont ->
      unwrap $ runG ggx $ \gx ->
        runStore . unwrap . first (\r -> store (r,)) $ runG gx cont

    {
      (runStore . unwrap . first (\r -> store (r,))) (r, s)
      = runStore . unwrap $ (store (r,), s)
      = runStore $ store (r,) s
      = ((r,), s)
      = first (,) (r,s)
      runStore . unwrap . first (\r -> store (r,)) = first (,)
    }

  = G $ \cont ->
      unwrap $ runG ggx $ \gx ->
        first (,) $ runG gx cont

  = G $ \cont ->
      unwrap . first (,) $ runG ggx $ \gx ->
        runG gx cont

  = G $ \cont ->
      runG ggx $ \gx ->
        runG gx cont

  = G $ \cont -> runG ggx $ \gx -> runG gx cont

  = joinG ggx

-}

instance Applicative (G s) where
  pure = pureG
  (<*>) = ap

instance Monad (G s) where
  ma >>= k = joinG $ fmap k ma

-- * Q

-- | @Q s@ is a @Monad@ isomorphic to @R ('Store' s)@   
newtype Q s a = Q { runQ :: (a -> s) -> (a, s) }
  deriving Functor

instance Applicative (Q s) where
  pure x = Q $ \f -> (x, f x)
  (<*>) = ap

instance Monad (Q s) where
  qx >>= k = joinQ (fmap k qx)

joinQ :: Q s (Q s a) -> Q s a
joinQ qqx = Q $ \f ->
  let (qx, s) = runQ qqx (\qx' -> snd (runQ qx' f))
      x = fst (runQ qx f)
  in (x, s)

fromRStore :: R (Store s) a -> Q s a
fromRStore rx = Q $ \f -> runR rx (\x -> store (x, ) (f x))

toRStore :: Q s a -> R (Store s) a
toRStore qx = R $ \k ->
  let (x,s) = runQ qx (pos . k)
  in peek s (k x)

-- `g2sc` function by @olf
-- https://discourse.haskell.org/t/a-new-kind-of-continuation-like-monad/10528/14
fromG :: G s a -> Q s a
fromG gx = Q $ \f -> runG gx (\x -> (x, f x))

-- the inverse of fromG
toG :: Q s a -> G s a
toG qx = G $ \k -> first (fst . k) (runQ qx (snd . k))

{-

(fromG, toG) is a pair of isomorphisms.

fromG (toG qx)
 = Q $ \f -> runG (toG qx) (\x -> (x, f x))
 = Q $ \f -> first (fst . (\x -> x, f x)) $ runQ qx (snd . (\x -> (x, f x)))
 = Q $ \f -> first id $ runQ qx f
 = Q $ \f -> runQ qx f
 = qx

toG (fromG gx)
 = G $ \k -> first (fst . k) (runQ (fromG gx (snd . k)))
 = G $ \k -> first (fst . k) $
     runG gx $ \x -> (x, snd (k x))
   -- Free theorem on (runG gx)
 = G $ \k ->
     runG gx $ \x -> first (fst . k) (x, snd (k x))
 = G $ \k ->
     runG gx $ \x -> (fst (k x), snd (k x))
 = G $ \k -> runG gx $ \x -> k x
 = G $ \k -> runG gx k
 = gx

fromG is a monad morphism.

fromG (pureG x)
 = Q $ \f -> runG (pureG x) (\x -> (x, f x))
 = Q $ \f -> (\cont -> cont x) (\x -> (x, f x))
 = Q $ \f -> (x, f x)
 = pure

fromG (joinG (fmap toG . toG $ qqx))
 = Q $ \f -> runG (joinG (fmap toG . toG $ qqx)) (\x -> (x, f x))
 = Q $ \f ->
    runG (fmap toG . toG $ qqx) $ \gx -> runG gx (\x -> (x, f x))
 = Q $ \f ->
    runG (toG qqx) $ \qx -> runG (toG qx) (\x -> (x, f x))
 = Q $ \f ->
    runG (toG qqx) $ \qx -> (\k -> first (fst . k) (runQ qx (snd . k))) (\x -> (x, f x))
 = Q $ \f ->
    runG (toG qqx) $ \qx -> runQ qx f
 = Q $ \f ->
    let k = \qx -> runQ qx f
    in first (fst . k) (runQ qqx (snd . k))
 = Q $ \f ->
    let k = \qx' -> runQ qx' f
        (qx, s) = runQ qqx (snd . k)
        x = (fst . k) qx
    in (x,s)
 = Q $ \f ->
    let (qx, s) = runQ qqx (\qx' -> snd (runQ qx' f))
        x = fst (runQ qx f)
    in (x,s)
 = joinQ qqx

-}

-- * SC

-- | @SC s@ is isomorphic to @Q s@.
--
--   It /looks/ like it is the product monad of 'Control.Monad.Trans.Select.Select' and
--   'Control.Monad.Trans.Cont.Cont' ...
--   but it isn't! The two components are not independent.
data SC s a = SC {
    runSelect :: (a -> s) -> a,
    runCont :: (a -> s) -> s
  }
  deriving Functor

instance Applicative (SC s) where
  pure = pureSC
  (<*>) = ap
instance Monad (SC s) where
  ma >>= k = joinSC (fmap k ma)

pureSC :: a -> SC s a
pureSC x = SC { runSelect = const x, runCont = ($ x) }

joinSC :: SC s (SC s a) -> SC s a
joinSC mmx = SC { runSelect = selPart, runCont = contPart }
  where
    contPart = \f -> runCont mmx (\mx -> runCont mx f)
    selPart = \f -> runSelect (runSelect mmx (\mx -> runCont mx f)) f

fromSC :: SC s a -> Q s a
fromSC mx = Q $ \f -> (runSelect mx f, runCont mx f)

toSC :: Q s a -> SC s a
toSC q = SC { runSelect = fst . runQ q, runCont = snd . runQ q }

-- | Continuation monad
newtype C s a = C { runC :: (a -> s) -> s }
  deriving Functor

pureC :: a -> C s a
pureC x = C ($ x)

joinC :: C s (C s a) -> C s a
joinC mmx = C $ \f -> runC mmx (\mx -> runC mx f)

-- | Selection monad
newtype S s a = S { runS :: (a -> s) -> a }
  deriving Functor

pureS :: a -> S s a
pureS x = S $ const x

joinS :: S s (S s a) -> S s a
joinS mmx = S $ \f -> runS (runS mmx (\mx -> f (runS mx f))) f