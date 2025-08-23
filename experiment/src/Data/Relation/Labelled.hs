{-# LANGUAGE ImportQualifiedPost #-}
module Data.Relation.Labelled(
  LabelledRel,
  lookup,
  transpose,
  unlabel,
  restrict
) where

import Prelude hiding (lookup)

import Data.Set qualified as Set
import Data.Set (Set)
import Data.Map qualified as Map
import Data.Map (Map)

import Data.Relation qualified as Rel
import Data.Relation (Rel)

type LabelledRel a label b = Map a (Map label (Set b))

unlabel :: Ord b => LabelledRel a label b -> Rel a b
unlabel = Map.map Set.unions

lookup :: Ord a => a -> LabelledRel a label b -> Map label (Set b)
lookup = Map.findWithDefault Map.empty

transpose :: (Ord a, Ord label, Ord b) => LabelledRel a label b -> LabelledRel b label a
transpose r =
  Map.unionsWith Rel.union
    [ Map.fromSet (const l2a) bs
      | (a,next) <- Map.toList r,
        (label,bs) <- Map.toList next,
        let l2a = Rel.singleton label a ]

notNull :: Foldable t => t a -> Maybe (t a)
notNull s = if null s then Nothing else Just s

restrict :: (Ord a, Ord b) => Set a -> Set b -> LabelledRel a label b -> LabelledRel a label b
restrict dom cod r = Map.mapMaybe (notNull . Map.mapMaybe (notNull . Set.intersection cod)) $ Map.restrictKeys r dom