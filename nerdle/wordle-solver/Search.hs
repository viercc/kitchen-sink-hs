{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}
module Search(
  -- * Abstract games
  AbstractGame,
  wordleToAbstract,
  restrictGame,

  -- * Strategy representation
  Strategy(..),
  interpretStrategy,

  -- ** Perfect strategy
  perfectStrategy,
  winningStrategyIn,

  -- ** Use of heuristics
  Score, Heuristic,
  heightHeuristic,
  informationHeuristic,
  minmaxHeuristic,

  heuristicStrategy
) where

import Prelude hiding (Word)

import Data.Ord (comparing)
import Data.Foldable

import qualified Data.Set as Set

import WordleLike

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV

import Data.IntSet (IntSet)

import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.Function (on)
import qualified Data.Map.Strict as Map
import Util (minmaxOf)
import Data.Maybe (listToMaybe)
import Data.Map.Strict (Map)
import Data.List (sortBy)
import Debug.Trace (trace)

-- * AbstractGame

data AbstractGame = AbstractGame {
    gameTable :: !(UV.Vector Int),
    gameTableWidth :: !Int,
    gameQueries :: !IntSet,
    gameAnswers :: !IntSet,
    gameAnswersSize :: !Int
  }
  deriving (Show)

getRow :: AbstractGame -> Int -> [Int]
getRow game x = [ tab UV.! (n * x + y) | y <- IntSet.toAscList ys ]
  where
    AbstractGame{ gameTable = tab, gameTableWidth = n, gameAnswers = ys} = game

data Part = Part {partSize :: !Int, partMembers :: !IntSet}

getRowPartition :: AbstractGame -> Int -> IntMap Part
getRowPartition game x =
    IntMap.fromListWith mergePart [ (tab UV.! (n * x + y), Part 1 (IntSet.singleton y)) | y <- IntSet.toAscList ys ]
  where
    AbstractGame{ gameTable = tab, gameTableWidth = n, gameAnswers = ys} = game
    mergePart (Part n1 p1) (Part n2 p2) = Part (n1 + n2) (IntSet.union p1 p2)

wordleToAbstract :: V.Vector Word -> AbstractGame
wordleToAbstract dict = trace ("build(" ++ show (V.length dict) ++")") $
  AbstractGame tab n allIxes allIxes n
  where
    n = V.length dict
    allIxes = IntSet.fromDistinctAscList [0 .. n - 1]
    tab
      | n == 0 = UV.empty
      | V.length (dict V.! 0) > 30 = UV.concat [ genRow i | i <- [0 .. n - 1] ]
      | otherwise = UV.generate (n * n) $ \idx ->
          let (queryId, answerId) = idx `quotRem` n
          in hashResponse (response (dict V.! answerId) (dict V.! queryId))
    
    genRow i = UV.fromListN n $ normalizeClasses $ [ response (dict V.! j) (dict V.! i) | j <- [0 .. n - 1]]

normalizeClasses :: Ord b => [b] -> [Int]
normalizeClasses = loop Map.empty
  where
    loop _ [] = []
    loop !subst (b:rest) = case Map.lookup b subst of
      Nothing ->
        let k = Map.size subst 
            subst' = Map.insert b k subst
        in k : loop subst' rest
      Just k -> k : loop subst rest

normalizeClassesInt :: [Int] -> [Int]
normalizeClassesInt = loop 0 IntMap.empty
  where
    loop _ _ [] = []
    loop !n !subst (b:rest) = case IntMap.lookup b subst of
      Nothing ->
        let subst' = IntMap.insert b n subst
        in n : loop (n + 1) subst' rest
      Just k -> k : loop n subst rest

restrictGame :: AbstractGame -> IntSet -> AbstractGame
restrictGame game@AbstractGame{
    gameTable = tab, gameTableWidth = n, gameQueries = xs, gameAnswers = ys1
  } ys2 = game{ gameQueries = xs', gameAnswers = ys, gameAnswersSize = ysSize }
  where
    ys = IntSet.intersection ys1 ys2
    ysSize = IntSet.size ys

    xs'
      | ysSize <= 1 = ys
      | ysSize <= 6 = IntSet.union ys (compact $ xs IntSet.\\ ys)
      | otherwise = IntSet.filter (not . isRedundant) xs
    
    getRow' x = [ tab UV.! (n * x + y) | y <- IntSet.toAscList ys ]

    isRedundant = isConstant . getRow'
    isConstant [] = True
    isConstant (a:as) = all (a ==) as

    sig = UV.fromListN ysSize . normalizeClassesInt . getRow'
    sigsSet = Set.fromList [ sig y | y <- IntSet.toList ys ]

    compact = IntSet.fromDistinctAscList . go sigsSet . IntSet.toAscList
      where
        go _ [] = []
        go visited (x:rest)
          | Set.member sig_x visited = go visited rest
          | otherwise                = x : go (Set.insert sig_x visited) rest
          where sig_x = sig x

-- * Strategy

data Strategy = Strategy {
    -- | The first move of the strategy
    stratMove :: !Int,
    -- | Strategies on the next turn
    stratNext :: IntMap Strategy
  }
  deriving Show

interpretStrategy :: V.Vector Word -> AbstractGame -> Strategy -> (Word, Map Response Strategy)
interpretStrategy dict game (Strategy move children) = (move', children')
  where
    move' = dict V.! move
    -- response-to-possible-answer map (r => min {y | y ∈ ys, response move' (dict ! y) == r})
    representatives = IntMap.fromListWith min $ zip (getRow game move) (IntSet.toAscList (gameAnswers game))

    children' = Map.fromList $ IntMap.elems $ IntMap.intersectionWith makeEntry representatives children
    makeEntry yRepr childStrat = (response (dict V.! yRepr) move', childStrat)

-- ** Perfect strategy

-- | Find some strategy with minimum worst-case length.
-- 
-- @perfectStrategy lb@ searches worst-case k-turns
-- winning strategy for @k <- [lb, lb+1, ..]@ 
perfectStrategy :: Int -> AbstractGame -> Strategy
perfectStrategy lb = searchLoop (max 1 lb)
  where
    searchLoop :: Int -> AbstractGame -> Strategy
    searchLoop k !game = 
      case trace ("perfect(depth=" ++ show k ++ ")") $ winningStrategyIn k game of
        Nothing -> searchLoop (k + 1) game
        Just x  -> x

-- >>> dict = fmap V.fromList $ V.fromList ["foo", "bar", "baz", "fox", "faz"]
-- >>> game = wordleToAbstract dict
-- >>> game
-- AbstractGame {gameTable = [63,21,21,61,53,21,63,61,21,29,21,61,63,21,31,61,21,21,63,53,53,29,31,53,63], gameTableWidth = 5, gameQueries = fromList [0,1,2,3,4], gameAnswers = fromList [0,1,2,3,4], gameAnswersSize = 5}
-- >>> restrictGame game (IntSet.fromList [1,2])
-- AbstractGame {gameTable = [63,21,21,61,53,21,63,61,21,29,21,61,63,21,31,61,21,21,63,53,53,29,31,53,63], gameTableWidth = 5, gameQueries = fromList [0,1,2], gameAnswers = fromList [1,2], gameAnswersSize = 2}
-- >>> winningStrategyIn 3 game
-- Just (Strategy {stratMove = 0, stratNext = fromList [(21,Strategy {stratMove = 1, stratNext = fromList [(61,Strategy {stratMove = 2, stratNext = fromList []})]}),(53,Strategy {stratMove = 4, stratNext = fromList []}),(61,Strategy {stratMove = 3, stratNext = fromList []})]})

-- | k-turns winning strategy (if exist)
winningStrategyIn :: Int -> AbstractGame -> Maybe Strategy
winningStrategyIn k game
  | k <= 0 = Nothing
  | k == 1 = case IntSet.toList (gameAnswers game) of
      [x] -> Just $ Strategy x IntMap.empty
      _ -> Nothing
  | otherwise = listToMaybe $ do
      x <- IntSet.toAscList (gameQueries game)
      subStrats <- toList $ traverse (subGame x) (getRowPartition game x)
      pure $ Strategy x (IntMap.mapMaybe id subStrats)
    where
      subGame x (Part n ys)
        | n == 1 && IntSet.member x ys = Just Nothing
        | otherwise = Just <$> winningStrategyIn (k - 1) (restrictGame game ys)

-- ** Heuristic strategy

-- | Score score (smaller is better)
type Score = Double
type Heuristic = AbstractGame -> Int -> Score

-- | @partitionHeight ps@ = number of possible answers, worst case
heightHeuristic :: Heuristic
heightHeuristic game x
  | IntMap.null ps' = (-1) / 0
  | otherwise = realToFrac (maximum ps')
  where
    game' = game{ gameAnswers = IntSet.delete x (gameAnswers game) }
    ps' = IntMap.fromListWith (+) [ (r,1 :: Int) | r <- getRow game' x ]

-- | Expected posterior entropy
informationHeuristic :: Heuristic
informationHeuristic game x
  | total == 0 = (-1) / 0
  | otherwise = info
  where
    game' = game{ gameAnswers = IntSet.delete x (gameAnswers game) }
    sizes = IntMap.elems $ IntMap.fromListWith (+) [ (r,1 :: Int) | r <- getRow game' x ]
    total = sum sizes

    info :: Double
    info = sum [n * log n | n <- realToFrac <$> sizes] / realToFrac total

-- | One step of minmax lookahead
minmaxHeuristic :: Heuristic -> Heuristic
minmaxHeuristic subHeuristic game x = negate $ minmaxOf negate
  [ [ subHeuristic game' x' | let game' = restrictGame game ys, x' <- IntSet.toList (gameQueries game')]
    | ys <- partMembers <$> IntMap.elems (getRowPartition game x) ]

heuristicStrategy :: Heuristic -> AbstractGame -> Strategy
heuristicStrategy heuristic game = Strategy bestMove children
  where
    bestMove = fst . minimumBy (comparing snd) . map (\x -> (x, heuristic game x)) $ IntSet.toList (gameQueries game)
    children = IntMap.mapMaybe subGame (getRowPartition game bestMove)
    subGame (Part _ ys)
      | bestMove `IntSet.member` ys = Nothing
      | otherwise = Just $ heuristicStrategy heuristic (restrictGame game ys)