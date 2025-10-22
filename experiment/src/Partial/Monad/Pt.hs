{- | Turn a PMonad to Monad -}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
module Partial.Monad.Pt(
  Pt(..)
) where

import Data.Coerce (coerce)

import Partial
import Partial.Functor
import Partial.Monad
import Witherable (Filterable (..))
import Control.Monad (ap)

-- | @PMonad m@ induces @Monad@ structure on @Maybe (m _)@.
--
-- === Examples
--
-- - @Pt (Either a) ~ Either (Maybe a)@
-- - @Pt ((,) a) ~ WriterT a Maybe@
-- - @Pt (These a) ~ MaybeT (Writer (Maybe a))@
-- - @Pt (Const Void) ~ Proxy@
-- - @Pt (These1 t u) ~ Product (Pt t) (Pt u)@
newtype Pt m a = Pt { unPt :: Maybe (m a) }
  deriving (Show, Eq, Functor)

instance PFunctor m => Filterable (Pt m) where
  mapMaybe f (Pt ma) = Pt $ ma >>= partialmap f

instance PMonad m => Applicative (Pt m) where
  pure = kleisliPt ppure
  (<*>) = ap

instance PMonad m => Monad (Pt m) where
  Pt ma >>= k = Pt $ ma >>= runPartial (pbind (unkleisliPt k))

kleisliPt :: (a -? m b) -> a -> Pt m b
kleisliPt = coerce

unkleisliPt :: (a -> Pt m b) -> (a -? m b)
unkleisliPt = coerce

-- >>> mxs = [Pt Nothing, Pt (Just Nothing), Pt (Just (Just 'x'))] :: [Pt Maybe Char]
-- >>> [mx >>= \x -> my >>= \y -> pure [x,y] | mx <- mxs, my <- mxs ]
-- [Pt {unPt = Nothing},      Pt {unPt = Nothing},      Pt {unPt = Nothing},
--  Pt {unPt = Just Nothing}, Pt {unPt = Just Nothing}, Pt {unPt = Just Nothing},
--  Pt {unPt = Nothing},      Pt {unPt = Just Nothing}, Pt {unPt = Just (Just "xx")}
-- ]
