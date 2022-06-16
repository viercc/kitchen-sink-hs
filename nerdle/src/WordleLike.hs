{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
module WordleLike(
  Response(..),
  response, addResponse,
  matches
) where

import Data.Functor.Rep
import Data.Bag qualified as Bag

import Data.Traversable ( mapAccumL )
import Data.Foldable (toList)
import Util (eqR)

data Response =
      Hit  -- ^ Green in Wordle, Black peg in MasterMind
    | Blow -- ^ Yellow in Wordle, White peg in MasterMind
    | Miss -- ^ Grey in Wordle, no pegs in MasterMind
    deriving (Show, Read, Eq, Ord, Enum, Bounded)

-- @response answer query@
response :: (Traversable v, Representable v, Ord char) => v char -> v char -> v Response
response answer query = snd $ mapAccumL step letterCounts (liftR2 (,) answer query)
  where
    letterCounts = Bag.fromList (toList answer)
    step lc (x,y) = case Bag.pullOut y lc of
      Nothing  -> (lc, Miss)
      Just lc' | x == y    -> (lc', Hit)
               | otherwise -> (lc', Blow)

addResponse :: (Traversable v, Representable v, Ord char) => v char -> v char -> v (char, Response)
addResponse answer query = liftR2 (,) query (response answer query)

matches :: (Traversable v, Representable v, Ord char) => v char -> v (char, Response) -> Bool
matches query hint = eqR (response query (fst <$> hint)) (snd <$> hint)
