{-# LANGUAGE BangPatterns #-}
module Util where

import Data.Foldable (Foldable (..))
import Data.Semigroup ( Max(..), Min(..) )
import Data.List (sortBy)

listSeq :: [a] -> b -> b
listSeq as u = foldl' (\b a -> seq a b) u as

minimumGroupBy :: (a -> a -> Ordering) -> [a] -> [a]
minimumGroupBy cmp = firstGroup . sortBy cmp
  where
    firstGroup [] = []
    firstGroup (a:as) = a : takeWhile (\b -> cmp a b == EQ) as

foldMapNonEmpty :: (Foldable t, Semigroup b) => (a -> b) -> t a -> b
foldMapNonEmpty f ta = case foldMap (Just . f) ta of
  Just b -> b
  Nothing -> error "foldMapNonEmpty: empty foldable"

minimumOf, maximumOf :: (Foldable t, Ord b) => (a -> b) -> t a -> b
minimumOf f = getMin . foldMapNonEmpty (Min . f)
maximumOf f = getMax . foldMapNonEmpty (Max . f)

minmaxOf :: (Foldable t, Foldable u, Ord b) => (a -> b) -> t (u a) -> b
minmaxOf f tu = case toList tu of
  [] -> error "minmaxOf: empty foldable"
  as0 : ass -> foldl' (maximumBelowOf f) (maximumOf f as0) ass

-- maximumBelow limit as = min limit (maximumOf as f)
maximumBelowOf :: (Foldable t, Ord b) => (a -> b) -> b -> t a -> b
maximumBelowOf f limit t = case map f (toList t) of
  [] -> error "maximumBelowOf: empty foldable"
  b:bs | b >= limit -> limit
       | otherwise  -> go b bs
  where
    go !bmax [] = bmax
    go !bmax (b:bs)
      | b >= limit = limit
      | otherwise  = go (max bmax b) bs
