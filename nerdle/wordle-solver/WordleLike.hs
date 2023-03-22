{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
module WordleLike(
  Response(..),
  response, addResponse,
  matches
) where

import Prelude hiding (zip, zipWith)
import Data.MultiSet qualified as Bag

import Data.Traversable ( mapAccumL )
import Data.Zip
import Data.Foldable (toList)

data Response =
      Hit  -- ^ Green in Wordle, Black peg in MasterMind
    | Blow -- ^ Yellow in Wordle, White peg in MasterMind
    | Miss -- ^ Grey in Wordle, no pegs in MasterMind
    deriving (Show, Read, Eq, Ord, Enum, Bounded)

pullOut :: Ord a => a -> Bag.MultiSet a -> Maybe (Bag.MultiSet a)
pullOut x bag
  | Bag.member x bag = Just (Bag.delete x bag)
  | otherwise = Nothing

-- @response answer query@
response :: (Traversable v, Zip v, Ord char) => v char -> v char -> v Response
response answer query = snd $ mapAccumL step letterCounts pairs
  where
    pairs = zip answer query
    letterCounts = Bag.fromList [ x | (x,y) <- toList pairs, x /= y ]
    step lc (x,y)
      | x == y = (lc, Hit)
      | otherwise = case pullOut y lc of
          Nothing  -> (lc, Miss)
          Just lc' -> (lc', Blow)

addResponse :: (Traversable v, Zip v, Ord char) => v char -> v char -> v (char, Response)
addResponse answer query = zip query (response answer query)

matches :: (Traversable v, Zip v, Ord char) => v char -> v (char, Response) -> Bool
matches query hint = and $ zipWith (==) (response query (fst <$> hint)) (snd <$> hint)
