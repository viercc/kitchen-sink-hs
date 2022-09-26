{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BangPatterns #-}
module Types where

import Prelude hiding (Word)
import qualified Data.Vector as V

import WordleLike ( Response(..) )
import Collection ( Collection(..) )

type Word = V.Vector Char
type Resp = V.Vector Response

showWordItem :: Collection Word i => i -> String
showWordItem = V.toList . itemValue

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
