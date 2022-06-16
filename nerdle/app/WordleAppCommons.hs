{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module WordleAppCommons where

import Prelude hiding (Word)
import Data.Foldable (minimumBy)
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
    charToResponse '-' = Just Miss
    charToResponse '+' = Just Blow
    charToResponse '#' = Just Hit
    charToResponse _   = Nothing

printResp :: Resp -> String
printResp = map responseChar . V.toList
  where
    responseChar Miss = '-'
    responseChar Blow = '+'
    responseChar Hit = '#'

type Strategy s k i = s -> (i, Map k s)

outcomes :: Collection Word i => i -> Set i -> Map Resp (Set i)
outcomes x ys = Map.fromListWith Set.union
  [ (resp y, Set.singleton y) | y <- Set.toList ys ]
  where
    resp y = response (itemValue y) (itemValue x)

type Score = (Int, Bool)
-- score is primarily the size of the largest groups.
-- In case of ties, "x can be the answer" choice
-- is preferred.
-- (Note that smaller = preffered here and True > False!)
maxSizeScore :: forall i. Collection Word i => i -> Set i -> (Score, (i, Map Resp (Set i)))
maxSizeScore x ys = ((maxGroupSize, x `Set.notMember` ys), (x, groups))
  where
    groups = outcomes x ys
    maxGroupSize = maximum (fmap Set.size groups)

minmaxSizeStrategy :: forall i. Collection Word i => Strategy (Set i) Resp i
minmaxSizeStrategy ys
  | Set.size ys <= 1 = (Set.findMin ys, Map.empty)
  | otherwise        = snd . minimumBy (comparing fst) $ map (\x -> maxSizeScore x ys) xs
  where
    xs = Set.toAscList universe :: [i]
