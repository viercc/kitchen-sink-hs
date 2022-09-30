{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Digit(Digit(..), digitsValue, integerToDigits, allDigits,
  Dec(..),
  Bit(..)
  ) where

import qualified Data.Char as Char
import Text.Read(Read(..), pfail)
import Data.Foldable (foldl')
import Data.Proxy (Proxy(..))

class (Ord d) => Digit d where
  radix :: Proxy d -> Int
  
  intToDigit :: Int -> Maybe d
  intToDigit n | 0 <= n && n < r = Just (unsafeIntToDigit n)
               | otherwise       = Nothing
    where r = radix @d Proxy

  unsafeIntToDigit :: Int -> d
  unsafeIntToDigit n = case intToDigit n of
    Nothing -> error "Out of bounds"
    Just d  -> d
  
  digitToInt :: d -> Int

  charToDigit :: Char -> Maybe d
  digitToChar :: d -> Char

newtype WrappedDigit d = WrapDigit d
  deriving newtype (Eq, Ord, Digit)

instance Digit d => Enum (WrappedDigit d) where
  fromEnum = digitToInt
  toEnum = unsafeIntToDigit

instance Digit d => Bounded (WrappedDigit d) where
  minBound = unsafeIntToDigit  0
  maxBound = unsafeIntToDigit (pred (radix @d Proxy))

instance Digit d => Show (WrappedDigit d) where
  show = pure . digitToChar

instance Digit d => Read (WrappedDigit d) where
  readPrec = readPrec >>= \n -> maybe pfail pure (intToDigit n)

digitsValue :: forall d. Digit d => [d] -> Integer
digitsValue ds = foldl' (\acc d -> r * acc + toInteger (digitToInt d)) 0 ds
  where r = toInteger $ radix @d Proxy

zeroDigit :: Digit d => d
zeroDigit = unsafeIntToDigit 0

integerToDigits :: forall d. Digit d => Integer -> [d]
integerToDigits n
  | n < 0  = error $ "integerToDigits: negative (" ++  show n ++ ")"
  | n == 0 = [zeroDigit]
  | otherwise = reverse $ go n
  where
    r = toInteger $ radix @d Proxy
    go 0 = []
    go x = case quotRem x r of
      (x', d) -> unsafeIntToDigit (fromInteger d) : go x'

allDigits :: forall d. Digit d => [d]
allDigits = unsafeIntToDigit <$> [0 .. r - 1]
  where r = radix @d Proxy

newtype Dec = MkDec { unDec :: Int }
  deriving newtype (Eq, Ord)
  deriving (Enum, Bounded, Show, Read) via (WrappedDigit Dec)

instance Digit Dec where
  radix _ = 10

  unsafeIntToDigit n | 0 <= n && n < 10 = MkDec n
                     | otherwise        = error $ "unsafeIntToDigit @Dec " ++ show n
    
  digitToInt = unDec
  
  digitToChar d = Char.intToDigit (unDec d)

  charToDigit c | Char.isDigit c = Just $ MkDec (Char.digitToInt c)
                | otherwise      = Nothing

newtype Bit = MkBit Bool
  deriving newtype (Eq, Ord)
  deriving (Enum, Bounded, Show, Read) via (WrappedDigit Bit)

instance Digit Bit where
  radix _ = 2

  unsafeIntToDigit 0 = MkBit False
  unsafeIntToDigit 1 = MkBit True
  unsafeIntToDigit n = error $ "unsafeIntToDigit @Bit " ++ show n
    
  digitToInt (MkBit b) = if b then 1 else 0
  
  charToDigit '0' = Just $ MkBit False
  charToDigit '1' = Just $ MkBit True
  charToDigit _ = Nothing
  
  digitToChar (MkBit b) = if b then '1' else '0'
