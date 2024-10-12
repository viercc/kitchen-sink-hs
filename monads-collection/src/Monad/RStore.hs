{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Monad.RStore where

import Control.Monad
import Control.Comonad
import Control.Comonad.Store

-- * R

-- | @R w@ is 'Monad' for every 'Comonad' @w@
newtype R w a = R { runR :: forall r. (a -> w r) -> r }
  deriving Functor

instance Comonad w => Applicative (R w) where
  pure x = R $ \k -> extract (k x)
  (<*>) = ap

instance Comonad w => Monad (R w) where
  rw >>= k = R $ \cont -> runR rw (\x -> runR (k x) (duplicate . cont))

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


-- * SC

-- | @SC s@ is isomorphic to @Q s@.
--
--   It /looks/ like it is the product monad of 'Control.Monad.Select.Select' and
--   'Control.Monad.Cont.Cont' ...
--   but it isn't! The two components are not independent.
data SC s a = SC {
    runSelect :: (a -> s) -> a,
    runCont :: (a -> s) -> s
  }
  deriving Functor

instance Applicative (SC s) where
  pure x = SC { runSelect = const x, runCont = ($ x) }
  (<*>) = ap

instance Monad (SC s) where
  ma >>= k = joinSC (fmap k ma)

joinSC :: SC s (SC s a) -> SC s a
joinSC mmx = SC { runSelect = selPart, runCont = contPart }
  where
    contPart = \f -> runCont mmx (\mx -> runCont mx f)
    selPart = \f -> runSelect (runSelect mmx (\mx -> runCont mx f)) f

fromSC :: SC s a -> Q s a
fromSC mx = Q $ \f -> (runSelect mx f, runCont mx f)

toSC :: Q s a -> SC s a
toSC q = SC { runSelect = fst . runQ q, runCont = snd . runQ q }