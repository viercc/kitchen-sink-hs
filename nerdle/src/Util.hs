module Util where

import Data.Traversable
import Data.Functor.Rep

eqR :: (Eq a, Foldable v, Representable v) => v a -> v a -> Bool
eqR xs ys = and $ liftR2 (==) xs ys

repFromList :: (Traversable t, Representable t) => [a] -> Maybe (t a)
repFromList as
    | length as == length t0 = Just $ snd $ mapAccumL step as t0
    | otherwise              = Nothing
  where
    t0 = pureRep ()
    step [] _ = error "unreachable!"
    step (a:as') _ = (as', a)
