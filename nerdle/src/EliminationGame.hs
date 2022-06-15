{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use sortOn" #-}
{-# LANGUAGE BangPatterns #-}
module EliminationGame where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Ord (comparing, Down (..))
import Data.List (sortBy)
import Data.Foldable (minimumBy)

class (Ord x) => Finite x where
    universe :: Set x

class (Finite x, Ord pred) => EliminationGame x pred | x -> pred where
    matches :: x -> pred -> Bool

    -- When @x == y@, @separator x y = []@.
    -- 
    -- When @x /= y@, @separator x y@ lists up @p :: pred@ such that
    -- @not (x `matches` p) && (y `matches` p)@.
    separator :: x -> x -> [pred]

maximalSets, minimalSets :: Ord k => [Set k] -> [Set k]
minimalSets = go . sortBy (comparing Set.size)
  where go [] = []
        go (x : xs) = x : go (filter (\y -> not (x `Set.isSubsetOf` y)) xs)
maximalSets = go . sortBy (comparing (Down . Set.size))
  where go [] = []
        go (x : xs) = x : go (filter (\y -> not (y `Set.isSubsetOf` x)) xs)

stepGame :: EliminationGame x pred => x -> Set x -> [Set x]
stepGame x s = maximalSets
  [ Set.filter (`matches` p) s | y <- Set.toList s, p <- separator x y ]

data Strategy x = Strategy {
        evaluation :: !Int,
        currentMove :: x,
        nextStrategy :: Set x -> Maybe (Strategy x)
    }

solve :: EliminationGame x pred => Strategy x
solve = undefined

mean :: [Double] -> Double
mean = go 0 0
  where
    go !t !n [] = t / n
    go !t !n (x:xs) = go (t + x) (n + 1) xs

randomOpponent :: EliminationGame x pred => (Set x -> Double) -> x -> Set x -> Double
randomOpponent eval x s = case stepGame x s of
    []    -> 0
    nexts -> mean (map eval nexts)

chooseBest :: EliminationGame x pred => (x -> Set x -> Double) -> Set x -> (x, Double)
chooseBest eval s
  | Set.size s <= 1 = (Set.findMin s, 0)
  | otherwise       = minimumBy (comparing snd) [ (x, eval x s) | x <- Set.toList universe ]

win0 :: Set x -> Double
win0 s | Set.size s <= 1 = 0
       | otherwise       = 1

win1, win2 :: EliminationGame x pred => Set x -> (x, Double)
win1 = chooseBest (randomOpponent win0)
win2 = chooseBest (randomOpponent (snd . win1))

remaining0 :: Set x -> Double
remaining0 s = realToFrac (max 0 (Set.size s - 1))

remaining1, remaining2 :: EliminationGame x pred => Set x -> (x, Double)
remaining1 = chooseBest (randomOpponent remaining0)
remaining2 = chooseBest (randomOpponent (snd . win1))
