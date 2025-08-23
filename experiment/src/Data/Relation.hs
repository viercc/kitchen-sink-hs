{-# LANGUAGE ImportQualifiedPost #-}
module Data.Relation(
  Rel,
  lookup,
  empty, singleton,
  union, transpose, compose,
  transitiveClosure,
  restrict
) where

import Prelude hiding (lookup)

import Data.Set qualified as Set
import Data.Set (Set)
import Data.Map qualified as Map
import Data.Map (Map)

type Rel a b = Map a (Set b)

empty :: Rel a b
empty = Map.empty

singleton :: a -> b -> Rel a b
singleton a b = Map.singleton a (Set.singleton b)

union :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
union = Map.unionWith Set.union

transpose :: (Ord a, Ord b) => Rel a b -> Rel b a
transpose r = foldl' union Map.empty
  [ Map.fromSet (const (Set.singleton a)) bs | (a,bs) <- Map.toList r ]

transitiveClosure :: Ord a => Map a (Set a) -> Map a (Set a)
transitiveClosure r = loop r
  where
    entireSet = Set.unions $ Map.keysSet r : Map.elems r
    identityRel = Map.fromSet Set.singleton entireSet
    r' = union identityRel r

    loop s
      | s == s' = s
      | otherwise = loop s'
      where s' = compose s r'

compose :: (Ord b, Ord c) => Rel a b -> Rel b c -> Rel a c
compose r s = Map.map (\bs -> Set.unions [lookup b s | b <- Set.toList bs]) r

lookup :: (Ord a, Ord b) => a -> Rel a b -> Set b
lookup = Map.findWithDefault Set.empty

notNull :: Set a -> Maybe (Set a)
notNull s = if null s then Nothing else Just s

restrict :: (Ord a, Ord b) => Set a -> Set b -> Rel a b -> Rel a b
restrict dom cod r = Map.mapMaybe (notNull . Set.intersection cod) $ Map.restrictKeys r dom