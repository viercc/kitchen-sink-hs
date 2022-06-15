{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
module WordleLike.Hint(
  Uncertain(..), Table,
  Hint(..),
  
  isCompleted, admits,
  
  noHint,
  responseToHint,
  mergeHint,
  mergeHints
) where

import Data.Functor.Rep
import Data.Bag qualified as Bag

import Data.Foldable (toList, foldlM)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Control.Monad (guard)
import Data.Monoid (Sum(..))
import Data.Bag (Bag)
import qualified Data.Set as Set

import WordleLike

data Uncertain a = Unknown | Known a
    deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

uncertainToMaybe :: Uncertain a -> Maybe a
uncertainToMaybe Unknown = Nothing
uncertainToMaybe (Known a) = Just a

class Unifiable a where
  unify :: a -> a -> Maybe a

instance Eq a => Unifiable (Uncertain a) where
  unify Unknown uy = Just uy
  unify ux Unknown = Just ux
  unify (Known x) (Known y) | x == y    = Just (Known x)
                            | otherwise = Nothing

unifyVec :: (Traversable v, Representable v, Unifiable a) => v a -> v a -> Maybe (v a)
unifyVec x y = sequenceA $ liftR2 unify x y

responseToHint :: (Traversable v, Representable v, Ord c) => v (c,Response) -> Hint v c
responseToHint qr= MkHint{ knownPos=knowns, possiblePos=poss, lowerCount=lowers, frozenChars = frozen }
  where
   knowns = (\(c,r) -> if r == Hit then Known c else Unknown) <$> qr
   lowers = Bag.fromList $ foldMap (\(c,r) -> [c | r /= Miss]) qr
   frozen = Set.fromList $ foldMap (\(c,r) -> [c | r == Miss]) qr
   poss = Map.fromListWith (liftR2 (&&)) [ (c,v) | (c, r) <- toList qr, r /= Miss, let v = possCond c <$> qr ]
   possCond c (c', Hit)  = c == c'
   possCond c (c', _)    = c /= c'

data Hint v c = MkHint { knownPos :: v (Uncertain c), possiblePos :: Table v c, lowerCount :: Bag c, frozenChars :: Set c }

deriving instance (forall x. Show x => Show (v x), Show c) => Show (Hint v c)

type Table v c = Map c (v Bool)

popCount :: Foldable v => v Bool -> Int
popCount = getSum . foldMap (\b -> if b then 1 else 0)

noHint :: (Representable v) => Hint v c
noHint = MkHint{ knownPos = pureRep Unknown, possiblePos = Map.empty, lowerCount=Bag.empty, frozenChars=Set.empty}

isCompleted :: (Traversable v) => Hint v c -> Maybe (v c)
isCompleted MkHint{ knownPos } = traverse uncertainToMaybe knownPos

admits :: (Traversable v, Representable v, Ord c) => Hint v c -> v c -> Bool
admits hint query = matchKnown && matchPossible && satisfyCount && satisfyFrozenCount
  where
    n = length query
    matchKnown = and $ liftR2 (\known c -> all (==c) known) (knownPos hint) query
    possible = possiblePos hint
    matchPossible = and $ imapRep (\i c -> maybe True (`index` i) $ Map.lookup c possible) query

    qCount = Bag.fromList (toList query)
    lCount = lowerCount hint
    frozen = frozenChars hint
    satisfyCount = Bag.isSubsetOf lCount qCount && Bag.size (Bag.union lCount qCount) <= n
    satisfyFrozenCount = all (\(c,k) -> Set.notMember c frozen || k == Bag.count c lCount) (Bag.toFreqs qCount)

mergeHint :: (Traversable v, Representable v, Ord c) => Hint v c -> Hint v c -> Maybe (Hint v c)
mergeHint h1 h2 = mergeHintStart h1 h2 >>= propagateLimits

mergeHints :: (Traversable v, Representable v, Ord c) => [Hint v c] -> Maybe (Hint v c)
mergeHints hints = foldlM mergeHintStart noHint hints >>= propagateLimits

mergeHintStart :: (Traversable v, Representable v, Ord c) => Hint v c -> Hint v c -> Maybe (Hint v c)
mergeHintStart !h1 !h2 = do
  knownPos' <- unifyVec (knownPos h1) (knownPos h2)
  let possiblePos' = Map.unionWith (liftR2 (&&)) (possiblePos h1) (possiblePos h2)
      lowerCount' = Bag.union (lowerCount h1) (lowerCount h2)
      frozenChars' = Set.union (frozenChars h1) (frozenChars h2)
  possiblePos' <- Just $ updateKnownPossible knownPos' possiblePos'
  guard $ all or possiblePos' -- All registered char must have at least one possible
  guard $ and (Map.intersectionWith (\lo candid -> lo <= popCount candid) (Bag.toFreqsMap lowerCount') possiblePos')

  pure $ MkHint knownPos' possiblePos' lowerCount' frozenChars'

updateKnownPossible :: (Traversable v, Representable v, Ord c) => v (Uncertain c) -> Table v c -> Table v c
updateKnownPossible known = Map.mapWithKey compatible
  where
    compatible c = liftR2 (\knownCell b -> b && all (== c) knownCell) known

propagateLimits :: (Traversable v, Representable v, Ord c) => Hint v c -> Maybe (Hint v c)
propagateLimits hint =
  do (needLoop, hint') <- propagateLimitsStep hint
     if needLoop
       then propagateLimits hint'
       else pure hint'

propagateLimitsStep :: (Traversable v, Representable v, Ord c) => Hint v c -> Maybe (Bool, Hint v c)
propagateLimitsStep hint@MkHint{ knownPos, possiblePos, lowerCount, frozenChars } = do
  frozenChars' <- case compare (Bag.size lowerCount) (length knownPos) of
    LT -> Just frozenChars
    EQ -> Just (frozenChars `Set.union` Map.keysSet (Bag.toFreqsMap lowerCount))
    GT -> Nothing

  let discoveries = do
        (c,n) <- Bag.toFreqs lowerCount
        let v = possiblePos Map.! c
        guard (n == popCount v)
        let newKnowledge = fmap (\b -> if b then Known c else Unknown) v
        [ (c, newKnowledge) ]
  frozenChars' <- Just $ Set.union frozenChars' (Set.fromList (fst <$> discoveries))
  knownPos' <- foldr (\va mvb -> mvb >>= \vb -> unifyVec va vb) (Just knownPos) (snd <$> discoveries)
  if and (liftR2 (==) knownPos knownPos')
    then pure (frozenChars /= frozenChars', hint{frozenChars = frozenChars'})
    else do let possiblePos' = updateKnownPossible knownPos' possiblePos
            pure (True, hint{knownPos = knownPos', possiblePos = possiblePos', frozenChars = frozenChars'})
