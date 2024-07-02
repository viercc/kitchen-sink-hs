{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
module Hopf where

import Data.Group
import Control.Comonad
import Data.Functor.Day
import Data.Functor.Day.Comonoid

-- | Hopf monoid of functors
--
-- ===== Laws
--
-- - @extract@ is an applicative morphism in the following sense:
--
--     - @extract (pure a) = a@
--     - @extract (x <*> y) = extract x $ extract y@
--
-- - @coapply@ is an applicative morphism
--
--     - @coapply (pure a) = pure a = Day (pure ()) (pure ()) (\_ _ -> a)@
--     - @coapply (x <*> y) = coapply x <*> coapply y@
--
-- - @antipode@ is the "inverse" of @<*>@.
--
--     - @dap . trans1 antipode . coapply = dap . trans2 antipode . coapply = pure . extract@
class (Applicative f, Comonoid f) => Hopf f where
  antipode :: f a -> f a

instance (Group g) => Hopf ((,) g) where
  antipode :: (g, a) -> (g, a)
  antipode (g1, x) = (invert g1, x)

instance (Group g) => Hopf ((->) g) where
  antipode :: (g -> a) -> (g -> a)
  antipode x = x . invert

-- * Example

data V3 a = V3 a a a
  deriving (Show, Eq, Functor)

instance Applicative V3 where
  pure x = V3 x x x
  V3 x0 x1 x2 <*> V3 y0 y1 y2 = V3 (x0 y0) (x1 y1) (x2 y2)

instance Comonad V3 where
  extract (V3 x0 _ _) = x0
  duplicate (V3 x0 x1 x2) = V3 (V3 x0 x1 x2) (V3 x1 x2 x0) (V3 x2 x0 x1)

instance Comonoid V3 where
  coapply (V3 x0 x1 x2) = Day (V3 0 1 2) (V3 0 1 2) $ \i j ->
    case (i + j) `mod` 3 of
      0 -> x0
      1 -> x1
      _ -> x2

instance Hopf V3 where
  antipode (V3 x0 x1 x2) = V3 x0 x2 x1

