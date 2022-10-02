{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}
module Search(outcomes, Score, scoreRespBy,
  minmaxSizeStrategy, heuristicStrategy, perfectStrategy
) where

import Prelude hiding (Word)

import Data.Ord (comparing)
import Data.Foldable
import Data.List (sortBy, partition)

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

isWinningResp :: Map Resp s -> Bool
isWinningResp m = Map.size m == 1 && all (==Hit) (fst (Map.findMin m))

trimMoves :: Collection Word i => [i] -> Set i -> [i]
trimMoves xs ys = xsAns ++ filter isEffective xsNonAns
  where
    (xsAns, xsNonAns) = partition (`Set.member` ys) xs
    isEffective x = case Set.minView ys of
          Nothing -> True
          Just (y0, ys') -> let r0 = resp y0 in all (\y -> resp y == r0) ys'
      where
        resp y = response (itemValue x) (itemValue y)

effectiveMoves :: Collection Word i => [i] -> Set i -> [(i, Map Resp (Set i))]
effectiveMoves xs ys = 
  [ (x, resps) | x <- xsAns, let resps = outcomes x ys ] ++
  [ (x, resps) | x <- xsNonAns, let resps = outcomes x ys, Map.size resps > 1 ]
  where
    (xsAns, xsNonAns) = partition (`Set.member` ys) xs

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
    results = [ (x, score) | (x, resp) <- effectiveMoves xs ys, let !score = scoreRespBy Set.size x resp ]
    xs' = map fst results
    winner = fst $ minimumBy (comparing snd) results

winsIn :: (a -> [b]) -> (b -> [a]) -> Int -> a -> Bool
winsIn opponent player = opponentTurn
  where
    opponentTurn n a = n > 0 && all (playerTurn n) (opponent a)
    playerTurn n a = any (opponentTurn (n-1)) (player a)

respOpponent :: Collection Word i => ([i], Map Resp (Set i)) -> [([i], Set i)]
respOpponent (xs, resp)
  | isWinningResp resp = []
  | otherwise          = [ (xs, ys') | ys' <- Map.elems resp ]

perfectStrategy :: forall i. Collection Word i => [i] -> Set i -> ([i], i)
perfectStrategy xs ys
  | Set.size ys <= 1 = ([], Set.findMin ys)
  | otherwise        = (xs', winner)
  where
    xs' = trimMoves xs ys
    winner = head [ x | maxDepth <- [1 .. ], x <- xs', winsIn' maxDepth (xs', outcomes x ys) ]
    winsIn' = winsIn respOpponent perfectPlayer

heuristicBranch :: forall i. Collection Word i => Int -> [i] -> Set i -> ([i], [i])
heuristicBranch width xs ys = (xs', candidates)
  where
    results = [ (x, score) | (x, resp) <- effectiveMoves xs ys, let !score = scoreRespBy Set.size x resp ]
    xs' = map fst results
    candidates = map fst $ take width $ sortBy (comparing snd) results

heuristicStrategy :: forall i. Collection Word i => Int -> [i] -> Set i -> ([i], i)
heuristicStrategy width xs ys
  | Set.size ys <= 1 = ([], Set.findMin ys)
  | otherwise        = (xs', winner)
  where
    (xs', candidates) = heuristicBranch width xs ys
    winner = head [ x | maxDepth <- [1 .. ], x <- candidates, winsIn' maxDepth (xs', outcomes x ys) ]
    winsIn' = winsIn respOpponent (heuristicPlayer width)

heuristicPlayer :: Collection Word i => Int -> ([i], Set i) -> [([i], Map Resp (Set i))]
heuristicPlayer width (xs, ys)
   | Set.size ys == 1 = [([y0], outcomes y0 ys)]
   | otherwise        = xs' `listSeq` [ (xs', outcomes x ys) | x <- candidates ]
  where
    y0 = Set.findMin ys
    (xs', candidates) = heuristicBranch width xs ys

perfectPlayer :: Collection Word i => ([i], Set i) -> [([i], Map Resp (Set i))]
perfectPlayer (xs, ys)
  | Set.size ys == 1 = [([y0], outcomes y0 ys)]
  | otherwise        = [(xs', outcomes x ys) | x <- xs']
  where
    y0 = Set.findMin ys
    xs' = trimMoves xs ys
