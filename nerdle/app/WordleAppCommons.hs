{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
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
import Control.Monad (guard)
import Data.Semigroup ( Max(..), Min(..) )
import Debug.Trace (traceShow, trace)

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

type Strategy s k i = s -> (i, Map k s)

outcomes :: Collection Word i => i -> Set i -> Map Resp (Set i)
outcomes x ys = endCorrectAnswer $ Map.fromListWith Set.union
  [ (resp y, Set.singleton y) | y <- Set.toList ys ]
  where
    resp y = response (itemValue y) xWord
    allHitResp = response xWord xWord
    xWord = itemValue x
    endCorrectAnswer = Map.adjust (const Set.empty) allHitResp
 
-- Score (smaller is better)
type Score = Int

maxSizeScore :: forall i. Collection Word i => i -> Set i -> (Score, (i, Map Resp (Set i)))
maxSizeScore x ys = (maxGroupSize, (x, groups))
  where
    groups = outcomes x ys
    maxGroupSize = maximum (fmap Set.size groups)

minmaxSizeStrategy :: forall i. Collection Word i => Strategy (Set i) Resp i
minmaxSizeStrategy ys
  | Set.size ys <= 1 = (Set.findMin ys, Map.empty)
  | otherwise        = snd . minimumBy (comparing fst) $ map (\x -> maxSizeScore x ys) xs
  where
    xs = Set.toAscList universe :: [i]

data GameTree x r ann = GameTree { gameAnnot :: ann, gameProgress :: Map x (Map r (GameTree x r ann)) }
    deriving (Show, Eq, Functor, Foldable, Traversable)

foldMapNonEmpty :: (Foldable t, Semigroup b) => (a -> b) -> t a -> b
foldMapNonEmpty f ta = case foldMap (Just . f) ta of
  Just b -> b
  Nothing -> error "foldMapNonEmpty: empty foldable"

minimumOf, maximumOf :: (Foldable t, Ord b) => t a -> (a -> b) -> b
minimumOf ta f = getMin $ foldMapNonEmpty (Min . f) ta
maximumOf ta f = getMax $ foldMapNonEmpty (Max . f) ta

completeGame :: forall i. Collection Word i => Set i -> GameTree i Resp ()
completeGame allWords = go allWords allWords
  where
    allHitResp = let x0 = itemValue (Set.findMin allWords) in response x0 x0

    go xs ys | Set.null ys = GameTree () Map.empty
             | otherwise   = GameTree () children
      where
        hands = do
            x <- Set.toAscList xs
            let responses = outcomes x ys
                isEffective = Map.size responses > 1 || Map.member allHitResp responses
            guard isEffective
            pure (x, responses)
        xs' = Set.fromAscList (fst <$> hands)
        children = Map.fromList
          [ (x, go xs' <$> rs) | (x, rs) <- hands ]

data GameLength = FinishIn !Int | Continues 
    deriving (Show, Eq, Ord)

winsInNTurns :: Int -> GameTree r x GameLength -> GameTree r x GameLength
winsInNTurns _ game@(GameTree (FinishIn _) _) = game
winsInNTurns n (GameTree Continues children)
  | Map.null children = GameTree (FinishIn 0) Map.empty
  | n <= 0 = GameTree Continues children
  | otherwise = traceShow newAnnot $ case newAnnot of
      FinishIn m -> GameTree (FinishIn (m + 1)) Map.empty
      Continues  -> GameTree Continues children'
      where
        children' = fmap (fmap (winsInNTurns (n - 1))) children
        newAnnot = minimumOf children' $ \rs -> maximumOf rs gameAnnot

iteratedWIN :: Int -> GameTree r x GameLength -> GameTree r x GameLength
iteratedWIN n
  | n <= 0 = id
  | otherwise = winsInNTurns n . trace ("iteratedWIN " ++ show n) . iteratedWIN (n - 1)

pruneContinues :: GameTree r x GameLength -> GameTree r x GameLength
pruneContinues (GameTree len children) = case len of
  Continues -> GameTree len Map.empty
  _         -> GameTree len (fmap (fmap pruneContinues) children)

pruneBadPlayerMoves :: (Ord x, Ord r, Ord score) => GameTree x r score -> GameTree x r score
pruneBadPlayerMoves (GameTree score children) = GameTree score children'
  where
    children' = Map.mapMaybe pruneResponses children
    pruneResponses rs | maxDepth >= score = Nothing
                      | otherwise         = Just rs
      where
        maxDepth = maximumOf rs gameAnnot

pruneBadMoves :: (Ord x, Ord r, Ord score) => GameTree x r score -> GameTree x r score
pruneBadMoves (GameTree score children) = GameTree score children'
  where
    children' = Map.mapMaybe pruneResponses children
    pruneResponses rs | maxDepth >= score = Nothing
                      | otherwise         = Just rs'
      where
        maxDepth = maximumOf rs gameAnnot
        rs' = Map.filter (\game -> gameAnnot game == score) rs

prettyPrintGameTree :: Show ann => (x -> String) -> (r -> String) -> GameTree x r ann -> String
prettyPrintGameTree showX showR = unlines . ppr 0
  where
    indent d = replicate (2*d) ' '
    ppr d (GameTree ann children) = (spaces ++ show ann) :
      do (x, rs) <- Map.toList children
         (r, game') <- Map.toList rs
         (spaces ++ showX x ++ " : " ++ showR r) : ppr (d+1) game'
      where
        spaces = indent d
