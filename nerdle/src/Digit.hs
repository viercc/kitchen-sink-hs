{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
module Digit(Digit, DecDigit(..), printDigit, charToDigit, decimalValue) where

import Data.Char ( intToDigit, isDigit, digitToInt )
import Text.Read(Read(..))
import Data.Foldable (foldl')

type Digit = DecDigit

newtype DecDigit = MkDec { unDec :: Int }
  deriving newtype (Show, Eq, Ord)

printDigit :: Digit -> Char
printDigit d = intToDigit (unDec d)

charToDigit :: Char -> Maybe Digit
charToDigit c | isDigit c = Just $ MkDec (digitToInt c)
              | otherwise = Nothing

decimalValue :: [Digit] -> Integer
decimalValue = foldl' (\r d -> 10 * r + toInteger (unDec d)) 0

instance Enum DecDigit where
    fromEnum (MkDec x) = x
    toEnum n | 0 <= n && n < 10 = MkDec n
             | otherwise        = error "Enum(Digit): out of bounds"

instance Bounded DecDigit where
    minBound = MkDec 0
    maxBound = MkDec 9

instance Read DecDigit where
  readPrec = readPrec >>= \n -> pure $! MkDec (fromInteger n)
