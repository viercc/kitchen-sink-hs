{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE UnboxedTuples              #-}
{-# LANGUAGE ViewPatterns               #-}
module Cardinality(
  Cardinality(),
  pattern Infty,
  pattern Overflowed,
  toInt)
where

import           GHC.Exts

import           Text.Read
import           Text.Read.Lex

newtype Cardinality = C Word
  deriving (Eq, Ord, Enum, Bounded)

pattern Infty :: Cardinality
pattern Infty <- C ((== maxBound) -> True)
          where Infty = C maxBound

pattern Overflowed :: Cardinality
pattern Overflowed <- C ((== pred maxBound) -> True)
          where Overflowed = C (pred maxBound)

{-# COMPLETE C #-}

instance Show Cardinality where
  show Infty      = "Infty"
  show Overflowed = "Overflowed"
  show (C n)      = show n

instance Read Cardinality where
  readPrec = cardinalityParser

cardinalityParser :: ReadPrec Cardinality
cardinalityParser =
  wrap (Infty <$ expect (Ident "Infty")) <++
  wrap (Overflowed <$ expect (Ident "Overflowed")) <++
  (checkOF <$> (readPrec :: ReadPrec Word))
  where
    wrap = readP_to_Prec . const

-- check overflow
checkOF :: Word -> Cardinality
checkOF c = C (min (pred maxBound) c)

negativeError :: a
negativeError = error "Cardinality:Negative"

nonzero# :: Int# -> Bool
nonzero# 0# = False
nonzero# _  = True

addWordF :: Word -> Word -> (Word, Bool)
addWordF (W# x#) (W# y#) =
  case addWordC# x# y# of
    (# z#, c# #) ->
      let !overf = nonzero# c# in (W# z#, overf)

timesWordF :: Word -> Word -> (Word, Bool)
timesWordF (W# x#) (W# y#) =
  case timesWord2# x# y# of
    (# hi#, lo# #) ->
      let !overf = nonzero# (gtWord# hi# 0##) in (W# lo#, overf)

instance Num Cardinality where
  fromInteger n
    | n < 0     = negativeError
    | n >= oft  = Overflowed
    | otherwise = C (fromInteger n)
       where oft = toInteger (pred maxBound :: Word)

  -- Addition
  Infty      + _          = Infty
  _          + Infty      = Infty
  -- It is not needed to handle Overflowed specially
  C a        + C b        =
    case addWordF a b of
      (_, True)  ->  Overflowed
      (c, False) -> checkOF c

  Infty      * 0          = error "Infty * 0"
  Infty      * _          = Infty
  0          * Infty      = error "0 * Infty"
  _          * Infty      = Infty
  -- It is not needed to handle Overflowed specially
  C a        * C b =
    case timesWordF a b of
      (_, True)  -> Overflowed
      (c, False) -> checkOF c

  (-) = error "Subtraction is not possible"
  negate = error "Negation is not possible"

  abs = id

  signum 0 = 0
  signum _ = 1

instance Real Cardinality where
  toRational = toRational . toInteger

instance Integral Cardinality where
  toInteger Infty      = error "toInteger Infty"
  toInteger Overflowed = error "toInteger Overflowed"
  toInteger (C c)      = toInteger c
  
  quotRem a b
    | a < Overflowed && b < Overflowed = coerce (quotRem :: Word -> Word -> (Word, Word)) a b
    | otherwise                        = error $ "quotRem " ++ show a ++ " " ++ show b

toInt :: Cardinality -> Maybe Int
toInt Infty      = Nothing
toInt Overflowed = Nothing
toInt (C c)      | c <= fromIntegral (maxBound :: Int) = Just $ fromIntegral c
                 | otherwise                           = Nothing
