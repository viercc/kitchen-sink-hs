{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# HLINT ignore "Use tuple-section" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Data.Functor.Curried where

import Control.Comonad
import Control.Monad
import Control.Monad.Trans
import Data.Functor.Day

-- | Curried (different but isomorphic to the one defined in kan-extensions)
newtype Curried f g a = Curried {runCurried :: forall r. f r -> g (a, r)}
  deriving (Functor)

curried :: (Functor h) => Curried (Day f g) h a -> Curried f (Curried g h) a
curried both =
  Curried $ \fr ->
    Curried $ \gs ->
      (\(a, (r, s)) -> ((a, r), s)) <$> runCurried both (Day fr gs (,))

uncurried :: (Functor h) => Curried f (Curried g h) a -> Curried (Day f g) h a
uncurried fgh =
  Curried $ \(Day fr gs op) ->
    let gh = runCurried fgh fr
        h = runCurried gh gs
     in (\((a, r), s) -> (a, op r s)) <$> h

pureC :: (Comonad f, Applicative g) => a -> Curried f g a
pureC x = Curried $ \fr -> pure (x, extract fr)

joinC :: (Comonad f, Monad g) => Curried f g (Curried f g a) -> Curried f g a
joinC mmx = Curried $ \fr ->
  do
    (mx, fr') <- runCurried mmx (duplicate fr)
    runCurried mx fr'

instance (Comonad f, Monad g) => Applicative (Curried f g) where
  pure = pureC
  (<*>) = ap

instance (Comonad f, Monad g) => Monad (Curried f g) where
  mx >>= k = joinC $ k <$> mx

instance (Comonad f) => MonadTrans (Curried f) where
  lift :: (Comonad f, Monad m) => m a -> Curried f m a
  lift gx = Curried $ \fr -> fmap (,extract fr) gx