{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}
module Search(outcomes, Score, scoreRespBy,
  minmaxSizeStrategy, lookAheadStrategy, recursiveDeepStrategy
) where

import Prelude hiding (Word)

import Data.Ord (comparing)
import Data.Foldable
import Data.List (sortBy)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Lazy as Map

import Collection
import WordleLike

import Types
import Util

outcomes :: Collection Word i => i -> Set i -> Map Resp (Set i)
outcomes x ys = Map.fromListWith Set.union [ (resp y, Set.singleton y) | y <- Set.toList ys ]
  where
    resp y = response (itemValue y) xWord
    xWord = itemValue x

isEffective :: Ord i => i -> Set i -> Map Resp (Set i) -> Bool
isEffective x ys resps = x `Set.member` ys || Map.size resps > 1

allEffectiveMoves :: Collection Word i => [i] -> Set i -> [(i, Map Resp (Set i))]
allEffectiveMoves xs ys =
  [ (x, resps) | x <- xs, let resps = outcomes x ys, isEffective x ys resps ]

-- Score (smaller is better)
type Score = Int

scoreRespBy :: forall i. Collection Word i => (Set i -> Score) -> i -> Map Resp (Set i) -> Score
scoreRespBy f x resps
    | isAnswer  = 0 
    | otherwise = maximumOf f resps
  where
    isAnswer = Map.elems resps == [Set.singleton x]

minmaxSizeStrategy :: forall i. Collection Word i => [i] -> Set i -> ([i], i)
minmaxSizeStrategy xs ys
  | Set.size ys <= 1 = ([], Set.findMin ys)
  | otherwise        = xs' `listSeq` (xs', winner)
  where
    results = [ (x, scoreRespBy Set.size x resps) | (x, resps) <- allEffectiveMoves xs ys ]
    xs' = map fst results
    isNotAnswer x = Set.notMember x ys
    winner = fst $ minimumBy (comparing snd <> comparing (isNotAnswer . fst)) results

lookAheadScore :: forall i. (Collection Word i) => i -> [i] -> Map Resp (Set i) -> (Score, Score)
lookAheadScore x xs' resps = (nextScore, currentScore)
  where
    currentScore = scoreRespBy Set.size x resps
    nextScore = scoreRespBy nextStateScore x resps
    nextStateScore ys' = minimum [ scoreRespBy Set.size x' resps' | (x', resps') <- allEffectiveMoves xs' ys' ]

lookAheadStrategy :: forall i. (Collection Word i) => [i] -> Set i -> ([i], i)
lookAheadStrategy xs ys
  | Set.size ys <= 1 = ([], Set.findMin ys)
  | otherwise        = xs' `listSeq` (xs', winner)
  where
    children = allEffectiveMoves xs ys
    xs' = map fst children
    results2 = [ (x, lookAheadScore x xs' resp) | (x, resp) <- children ]
    isNotAnswer x = Set.notMember x ys
    winner = fst $ minimumBy (comparing snd <> comparing (isNotAnswer . fst)) results2

recursionWidth :: Int
recursionWidth = 10

recursiveDeepStrategy :: forall i. Collection Word i => [i] -> Set i -> ([i], i)
recursiveDeepStrategy xs ys
  | Set.size ys <= 1 = ([], Set.findMin ys)
  | otherwise        = (xs', winner)
  where
    (xs', candidates) = recursiveDeepBranch xs ys
    winner = head [ x | maxDepth <- [1 .. ], x <- candidates, winsIn maxDepth xs x ys ]

recursiveDeepBranch :: forall i. Collection Word i => [i] -> Set i -> ([i], [i])
recursiveDeepBranch xs ys
   | Set.size ys == 1 = ([y0], [y0])
   | otherwise        = xs' `listSeq` (xs', candidates)
  where
    y0 = Set.findMin ys
    results = [ (x, scoreRespBy Set.size x resp) | (x, resp) <- allEffectiveMoves xs ys ]
    xs' = map fst results
    isNotAnswer x = Set.notMember x ys
    candidates = map fst $ take recursionWidth $ sortBy (comparing snd <> comparing (isNotAnswer . fst)) results

winsIn :: forall i. Collection Word i => Int -> [i] -> i -> Set i -> Bool
winsIn 0 _ x ys = ys == Set.singleton x
winsIn n xs x ys = ys == Set.singleton x || all subStep (outcomes x ys)
  where
    subStep ys' =
      let (xs', candidates) = recursiveDeepBranch xs ys'
      in  any (\x' -> winsIn (n-1) xs' x' ys') candidates
