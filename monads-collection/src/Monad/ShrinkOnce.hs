{-# LANGUAGE DeriveFunctor #-}
module Monad.ShrinkOnce(
  Once(..),
  shrinkOnce
) where

import Control.Applicative

data Once a = Once { getDefault :: a
                   , getVariants :: [a] }
  deriving (Show, Read, Eq, Ord, Functor)

instance Applicative Once where
  pure a = Once a []
  liftA2 op (Once a as) (Once b bs) =
    Once (a `op` b) (fmap (a `op`) bs ++ fmap (`op` b) as)

instance Monad Once where
  return = pure
  Once a as >>= k =
    let Once b bs1 = k a
        bs2 = getDefault . k <$> as
    in Once b (bs1 ++ bs2)

-- | Apply shrinking function to one of elements of a traversable container.
shrinkOnce :: (Traversable t) => (a -> [a]) -> t a -> [t a]
shrinkOnce f = getVariants . traverse (\a -> Once a (f a))
