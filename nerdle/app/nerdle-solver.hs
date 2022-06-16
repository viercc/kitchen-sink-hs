{-# LANGUAGE DerivingStrategies, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Prelude hiding (Word)
import Control.Monad ((>=>))
import Data.Foldable (toList)
import Data.Ord (comparing, Down(..))
import Data.List (sortBy, minimumBy, maximumBy)

import System.IO
import System.Exit
import System.Environment (getArgs)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import qualified Data.Vector as V

import Collection
import V8
import Util
import WordleLike

type V = V8
type Option = FilePath
type Word = V Char
newtype Hint = Hint (V (Char, Response))
     deriving (Eq, Ord)

getOption :: IO Option
getOption = getArgs >>= \args -> case args of
    [] -> pure "list-nerdle.txt"
    (fileName:_) -> pure fileName

readWordListFile :: FilePath -> IO [Word]
readWordListFile fileName = do
    wordTxt <- readFile' fileName
    case traverse repFromList (lines wordTxt) of
        Nothing -> exitFailure
        Just ws -> pure ws

main :: IO ()
main = do
    inFile <- getOption
    ws <- readWordListFile inFile
    let n = length ws
    putStrLn $ "Read " ++ show inFile ++ ": " ++ show n ++ " words loaded"
    withCollection (V.fromList ws) solverMain

solverMain :: (Collection Word i) => Set i -> IO ()
solverMain coll = do
    --print (minmaxSizeStrategy coll)
    print result
  where
    result = map (toList . itemValue) . snd $ worstCase minmaxSizeStrategy coll

maximalSets, minimalSets :: Ord k => [Set k] -> [Set k]
minimalSets = go . sortBy (comparing Set.size)
  where go [] = []
        go (x : xs) = x : go (filter (\y -> not (x `Set.isSubsetOf` y)) xs)
maximalSets = go . sortBy (comparing (Down . Set.size))
  where go [] = []
        go (x : xs) = x : go (filter (\y -> not (y `Set.isSubsetOf` x)) xs)

type Strategy s i = s -> (i, (Int, [s]))

minmaxSizeStrategy :: forall i. Collection Word i => Strategy (Set i) i
minmaxSizeStrategy ys
  | Set.size ys <= 1 = (Set.findMin ys, (0, []))
  | otherwise        = minimumBy (comparing (fst . snd)) (map children xs)
  where
    xs = Set.toAscList universe :: [i]
    children x = (x, (maxGroupSize, nexts))
      where
        resp y = response (itemValue y) (itemValue x)
        groups = Map.fromListWith Set.union
           [ (resp y, Set.singleton y) | y <- Set.toList ys ]
        nexts = Map.elems groups
        maxGroupSize = maximum (map Set.size nexts)

data GameTree = GameTree !Word [(V8 Response, GameTree)]
  deriving Show

worstCase :: Strategy s i -> s -> (Int, [i])
worstCase strat s = case strat s of
    (x, (_, [])) -> (1, [x])
    (x, (_, nexts)) -> case maximumBy (comparing fst) (map (worstCase strat) nexts) of
        ~(n, xs) -> (n + 1, x : xs)
