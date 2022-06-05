{-# LANGUAGE ImportQualifiedPost #-}
module MasterMind where

import Data.Functor.Rep
import Data.Map.Strict qualified as Map
import Data.Bag qualified as Bag
import Data.Traversable
import Data.Foldable (toList)

data Response =
      Hit  -- ^ Green in Wordle, Black peg in MasterMind
    | Blow -- ^ Yellow in Wordle, White peg in MasterMind
    | Miss -- ^ Grey in Wordle, no pegs in MasterMind

-- Checks if the response is valid
response :: (Traversable v, Representable v, Ord char) => v char -> v char -> v Response
response xs ys = respBlows $ respHits xs ys

respHits :: (Representable v, Eq char) => v char -> v char -> v (Either Response (char, char))
respHits = liftR2 both
  where
    both x y | x == y    = Left Hit
             | otherwise = Right (x,y)

respBlows :: (Traversable v, Ord char) => v (Either Response (char, char)) -> v Response
respBlows rs =
    let letterCounts = Bag.fromList [ x | Right (x,_) <- toList rs ]
    in  snd $ mapAccumL step letterCounts rs
  where
    step lc resp = case resp of
        Left a       -> (lc, a)
        Right (x, y) -> case Bag.pullOut y lc of
            Nothing  -> (lc, Miss)
            Just lc' -> (lc', Blow)
