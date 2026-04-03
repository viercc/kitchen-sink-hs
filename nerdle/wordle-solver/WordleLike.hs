{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
module WordleLike(
  Resp(..), Response,
  Word, response, isWin,
  
  charToResp, respToChar,
  readResponse, showResponse,
  hashResponse
) where

import Prelude hiding (Word, zip, zipWith)
import Data.MultiSet qualified as Bag

import Data.Traversable ( mapAccumL )
import Data.Foldable (toList)

import qualified Data.Vector as V
import Data.Bits (Bits(shiftL, (.|.)), FiniteBits (..))

data Resp =
      Hit  -- ^ Green in Wordle, Black peg in MasterMind
    | Blow -- ^ Yellow in Wordle, White peg in MasterMind
    | Miss -- ^ Grey in Wordle, no pegs in MasterMind
    deriving (Show, Read, Eq, Ord, Enum, Bounded)

pullOut :: Ord a => a -> Bag.MultiSet a -> Maybe (Bag.MultiSet a)
pullOut x bag
  | Bag.member x bag = Just (Bag.delete x bag)
  | otherwise = Nothing

-- @response answer query@
response :: (Ord char) => V.Vector char -> V.Vector char -> Response
response answer query = snd $ mapAccumL step letterCounts pairs
  where
    pairs = V.zip answer query
    letterCounts = Bag.fromList [ x | (x,y) <- toList pairs, x /= y ]
    step lc (x,y)
      | x == y = (lc, Hit)
      | otherwise = case pullOut y lc of
          Nothing  -> (lc, Miss)
          Just lc' -> (lc', Blow)

isWin :: Response -> Bool
isWin = V.all (== Hit)

type Word = V.Vector Char
type Response = V.Vector Resp

charToResp :: Char -> Maybe Resp
charToResp '.' = Just Miss
charToResp '?' = Just Blow
charToResp '#' = Just Hit
charToResp _   = Nothing

readResponse :: String -> Maybe Response
readResponse = fmap V.fromList . traverse charToResp

respToChar :: Resp -> Char
respToChar Miss = '.'
respToChar Blow = '?'
respToChar Hit = '#'

showResponse :: Response -> String
showResponse = map respToChar . V.toList

intBitWidth :: Int
intBitWidth = finiteBitSize (undefined :: Int)

-- | Make a perfect hash of @Response@
--   but only for length up to @intBitWidth `div` 2@.
hashResponse :: Response -> Int
hashResponse r
  | 2 * V.length r > intBitWidth = error "Too large response to encode"
  | otherwise = V.foldl' step 0 r
    where
      respToBits respSymbol = case respSymbol of
        Miss -> 1
        Blow -> 2
        Hit -> 3
      step h respSymbol = shiftL h 2 .|. respToBits respSymbol
