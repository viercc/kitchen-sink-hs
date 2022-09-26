{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}
module WordleAppCommons where

import Prelude hiding (Word)
import Data.Foldable (minimumBy, Foldable (..))
import Data.Ord (comparing)

import System.IO
import System.Exit (exitFailure)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import qualified Data.Vector as V

import Collection
import WordleLike
import Data.Semigroup ( Max(..), Min(..) )
import Data.List (sortBy)
import Data.Bifunctor

type Word = V.Vector Char
type Resp = V.Vector Response

readWordListFile :: FilePath -> IO [Word]
readWordListFile fileName = do
    wordTxt <- readFile' fileName
    let ws = map V.fromList $ filter (not . null) (lines wordTxt)
    case ws of
        [] -> hPutStrLn stderr "Empty word list!" >> exitFailure
        w:ws' | all (\v -> length w == length v) ws' -> pure ws
              | otherwise                            -> hPutStrLn stderr "Word length varies!" >> exitFailure

promptMap :: (Ord k) => String -> (String -> Maybe k) -> Map k a -> IO a
promptMap msg reader dict = go
  where
    go =
      do putStr msg
         hFlush stdout
         s <- getLine
         case reader s of
             Nothing -> putStrLn "No parse, try again" >> go
             Just k -> case Map.lookup k dict of
                 Nothing -> putStrLn "Key not found, try again" >> go
                 Just a  -> pure a

readResp :: String -> Maybe Resp
readResp = fmap V.fromList . traverse charToResponse
  where
    charToResponse '.' = Just Miss
    charToResponse '?' = Just Blow
    charToResponse '#' = Just Hit
    charToResponse _   = Nothing

printResp :: Resp -> String
printResp = map responseChar . V.toList
  where
    responseChar Miss = '.'
    responseChar Blow = '?'
    responseChar Hit = '#'

outcomes :: Collection Word i => i -> Set i -> Map Resp (Set i)
outcomes x ys
  | ys == Set.singleton x = Map.singleton (resp x) (Set.singleton x)
  | otherwise             = Map.fromListWith Set.union [ (resp y, Set.singleton y) | y <- Set.toList ys, y /= x ]
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
minmaxSizeStrategy xs ys = second head $ minmaxSizeStrategyAll xs ys

listSeq :: [a] -> b -> b
listSeq as u = foldl' (\b a -> seq a b) u as

minmaxSizeStrategyAll :: forall i. Collection Word i => [i] -> Set i -> ([i], [i])
minmaxSizeStrategyAll xs ys
  | Set.size ys <= 1 = ([], [Set.findMin ys])
  | otherwise        = xs' `listSeq` (xs', winners)
  where
    results = [ (x, scoreRespBy Set.size x resps) | (x, resps) <- allEffectiveMoves xs ys ]
    xs' = map fst results
    winners = map fst $ minimumGroupBy (comparing snd) results

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
    winner = fst $ minimumBy (comparing snd) results2

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
    candidates = map fst $ take recursionWidth $ sortBy (comparing snd) results

winsIn :: forall i. Collection Word i => Int -> [i] -> i -> Set i -> Bool
winsIn 0 _ x ys = ys == Set.singleton x
winsIn n xs x ys = ys == Set.singleton x || all subStep (outcomes x ys)
  where
    subStep ys' =
      let (xs', candidates) = recursiveDeepBranch xs ys'
      in  any (\x' -> winsIn (n-1) xs' x' ys') candidates

---------------

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
