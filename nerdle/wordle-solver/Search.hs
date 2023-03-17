{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
module Search(outcomes,
  simplePlay,
  Strategy(..),
  simpleStrategy, heuristicStrategy, perfectStrategy
) where

import Prelude hiding (Word)

import Data.Ord (comparing, Down (..))
import Data.Foldable
import Data.List (partition, sortOn)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Lazy as Map

import Collection
import WordleLike

import Types
import Util

import GameTree (Nat(..), minimumNat, maximumNat)
import Data.Bifunctor (Bifunctor(..))
import Data.Either (partitionEithers)

outcomes :: Collection Word i => i -> Set i -> Map Resp (Set i)
outcomes x ys = Map.fromListWith Set.union (resp <$> Set.toList ys)
  where
    resp y | x == y    = (response xWord xWord, Set.empty)
           | otherwise = (response (itemValue y) xWord, Set.singleton y)
    xWord = itemValue x

effectiveMoves :: Collection Word i => [i] -> Set i -> [(i, Map Resp (Set i))]
effectiveMoves xs ys = 
  [ (x, resps) | x <- xsAns, let resps = outcomes x ys ] ++
  [ (x, resps) | x <- xsNonAns, let resps = outcomes x ys, Map.size resps > 1 ]
  where
    (xsAns, xsNonAns) = partition (`Set.member` ys) xs

-- | Heuristic Score (smaller is better)
type Score = Int

scoreResp :: forall i. Collection Word i => Map Resp (Set i) -> Score
scoreResp = maximumOf Set.size

simplePlay :: forall i. Collection Word i => [i] -> Set i -> ([i], i)
simplePlay xs ys
  | Set.size ys <= 1 = ([], Set.findMin ys)
  | otherwise        = xs' `listSeq` (xs', winner)
  where
    results = [ (x, score) | (x, resp) <- effectiveMoves xs ys, let !score = scoreResp resp ]
    xs' = map fst results
    winner = fst $ minimumBy (comparing snd) results

----------------------

data Strategy i = Strategy { _bestPlay :: i, _nextState :: Map Resp (Strategy i) } | AlreadyWon
   deriving Show

simpleStrategy :: forall i. Collection Word i => Strategy i
simpleStrategy = go (Set.toList universe) universe
  where
    go xs ys = case Set.toList ys of
      []   -> AlreadyWon
      [y0] -> Strategy { _bestPlay = Set.findMin ys, _nextState = AlreadyWon <$ outcomes y0 ys }
      _    -> Strategy { _bestPlay = winner, _nextState = go xs' <$> winnerResp }
      where
        results = sortOn (scoreResp . snd) $ effectiveMoves xs ys
        xs' = map fst results
        (winner, winnerResp) = head results

data GameTree s i = GameTree { _gameState :: s, _playerMoves :: [(i, Map Resp (GameTree s i))] }

calcGuessedDepth :: (Ord a) => Int -> (s -> a)
  -> (s -> Bool) -> GameTree s i -> GameTree (s, Nat) i
calcGuessedDepth width stateScore isWin = go
  where
    getScore = stateScore . fst . _gameState
    getDepth = snd . _gameState
    respScore = maximumOf getScore
    limitResp = take width . sortOn (Down . getScore) . Map.elems
    go (GameTree s playerMoves)
      | isWin s = GameTree (s, Zero) []
      | otherwise =
          let playerMoves' = fmap (fmap (fmap go)) playerMoves
              limitedPlayerMoves = take width $ sortOn respScore $ map snd playerMoves'
              w = minimumNat $ maximumNat . fmap getDepth . limitResp <$> limitedPlayerMoves
          in GameTree (s, Succ w) playerMoves'

depthStrategy :: GameTree (s, Nat) i -> Strategy i
depthStrategy (GameTree (_,d) moves) =
  let moves' = [ (i, resp) | (i, resp) <- moves, all (\next -> snd (_gameState next) < d) resp ]
   in case moves' of
        [] -> AlreadyWon
        (i,resp) : _ -> Strategy i (depthStrategy <$> resp)

----------------------

data GameState i = GameState { _moveCandidates :: [i], _solutionSet :: Set i }

isWinState :: GameState i -> Bool
isWinState GameState{ _solutionSet = ys } = Set.null ys

makeGameTree :: Collection Word i => GameTree (GameState i) i
makeGameTree = GameTree s0 firstMoves
  where
    ys = universe
    xs = Set.toList ys
    s0 = GameState xs ys
    subTree ys' = makeGameTreeSub (GameState xs ys')
    firstMoves = [ (x, subTree <$> resp) | x <- xs, let resp = outcomes x ys ]

makeGameTreeSub :: Collection Word i => GameState i -> GameTree (GameState i) i
makeGameTreeSub s@(GameState xs ys) = GameTree s nexts
  where
    moves = sortOn (scoreResp . snd) $ effectiveMoves xs ys
    xs' = map fst moves
    subTree ys' = makeGameTreeSub (GameState xs' ys')
    nexts = [ (x, subTree <$> resp) | (x, resp) <- moves ]

perfectStrategy :: forall i. Collection Word i => Strategy i
perfectStrategy = perfectStrategyFrom makeGameTree

perfectStrategyFrom :: Collection Word i => GameTree (GameState i) i -> Strategy i
perfectStrategyFrom = recoverMissingStrat . iteratedDeepening isWinState 1

recoverMissingStrat :: Collection Word i => Strategy i -> Strategy i
recoverMissingStrat = go universe
  where
    xs0 = Set.toList universe
    go ys strat = case strat of
      AlreadyWon -> AlreadyWon
      Strategy x plans -> Strategy x (repairWith plans (outcomes x ys))
      where
        coverUp plans k ys' =
          case Map.lookup k plans of
            Just nextStrat -> nextStrat
            Nothing -> perfectStrategyFrom $ makeGameTreeSub (GameState xs0 ys')
        repairWith plans = Map.mapWithKey (coverUp plans)

iteratedDeepening :: (s -> Bool) -> Int -> GameTree s i -> Strategy i
iteratedDeepening isWin depth tree =
  case tryFindStrategyIn isWin depth tree of
    Left tree' -> iteratedDeepening isWin (depth + 1) tree'
    Right strat -> strat

tryFindStrategyIn :: (s -> Bool) -> Int -> GameTree s i -> Either (GameTree s i) (Strategy i)
tryFindStrategyIn isWin depth (GameTree s moves)
  | isWin s    = Right AlreadyWon
  | depth <= 0 = Left (GameTree s moves)
  | otherwise = case partitionEithers (map splitMove moves) of
      (moves', []) -> Left (GameTree s moves')
      (_, (i, strat) : _) -> Right (Strategy i strat)
  where
    splitResps resp = case Map.mapEither (tryFindStrategyIn isWin (depth-1)) resp of
      (misses, strat) | Map.null misses -> Right strat
                      | otherwise       -> Left misses
    splitMove (i, resp) = bimap (i,) (i,) (splitResps resp)


heuristicStrategy :: forall i. Collection Word i => Int -> Strategy i
heuristicStrategy width = depthStrategy $ calcGuessedDepth width (Set.size . _solutionSet) isWinState makeGameTree