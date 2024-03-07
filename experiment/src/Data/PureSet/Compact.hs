{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

-- | Hereditarily finite set
module Data.PureSet.Compact
  ( Set (),
    toAscList, toDescList,

    toNatural, fromNatural,

    showAckermann,
  )
where

import Data.Bits
import Data.List (foldl', intersperse)
import qualified Data.Set as D
import qualified Data.Set.Extra as D
import Data.Word (Word64)
import Math.NumberTheory.Logarithms (naturalLog2)
import Numeric.Natural (Natural)
import Prelude hiding (null)

import Data.PureSet.Class

type SmallNat = Word64

wordSize :: SmallNat
wordSize = fromIntegral $ finiteBitSize (0 :: SmallNat)

data Set
  = MkSet
      !(D.Set Set)
      -- ^ Large part
      !SmallNat
      -- ^ Small part
  deriving (Eq)

-- | The order which does not change by bijections 'toNatural' and 'fromNatural'
instance Ord Set where
  compare (MkSet xlarge x) (MkSet ylarge y) =
    compare (D.toDescList xlarge) (D.toDescList ylarge) <> compare x y

instance Show Set where
  showsPrec = defaultShowsPrec

instance IsList Set where
  type Item Set = Set

  fromList = foldl' (flip insert) empty
  toList = Data.PureSet.Compact.toAscList

----

instance SetModel Set where
  null :: Set -> Bool
  null (MkSet xlarge x) = x == 0 && D.null xlarge

  size :: Set -> Int
  size (MkSet xlarge x) = D.size xlarge + popCount x

  member :: Set -> Set -> Bool
  member x (MkSet ylarge y) = case matchSmall x of
    Nothing -> D.member x ylarge
    Just x' -> testBit y x'

  empty :: Set
  empty = MkSet D.empty 0

  singleton :: Set -> Set
  singleton x = case matchSmall x of
    Nothing -> MkSet (D.singleton x) 0
    Just x' -> MkSet D.empty (bit x')

  union :: Set -> Set -> Set
  union (MkSet xlarge x) (MkSet ylarge y) = MkSet (D.union xlarge ylarge) (x .|. y)

  bigUnion :: Set -> Set
  bigUnion (MkSet xlarge x) = D.foldl' union (MkSet D.empty (unionPositions64 x)) xlarge

  intersection :: Set -> Set -> Set
  intersection (MkSet xlarge x) (MkSet ylarge y) = MkSet (D.intersection xlarge ylarge) (x .&. y)

  difference :: Set -> Set -> Set
  difference (MkSet xlarge x) (MkSet ylarge y) = MkSet (D.difference xlarge ylarge) (x .&. complement y)

  symdiff :: Set -> Set -> Set
  symdiff (MkSet xlarge x) (MkSet ylarge y) = MkSet (D.symdiff xlarge ylarge) (x `xor` y)

  -- | insert x y = union (singleton x) y
  insert :: Set -> Set -> Set
  insert x (MkSet ylarge y) = case matchSmall x of
    Nothing -> MkSet (D.insert x ylarge) y
    Just x' -> MkSet ylarge (setBit y x')

  -- | delete x y = difference y (singleton x)
  delete :: Set -> Set -> Set
  delete x (MkSet ylarge y) = case matchSmall x of
    Nothing -> MkSet (D.delete x ylarge) y
    Just x' -> MkSet ylarge (clearBit y x')

-- | If a given set is "small", return its encoding.
--   (the encoding /e/ of a small set is in 0 <= /e/ < 64)
matchSmall :: Set -> Maybe Int
matchSmall (MkSet xlarge x)
  | D.null xlarge && x < wordSize = toIntegralSized x
  | otherwise = Nothing

toAscList :: Set -> [Set]
toAscList (MkSet xlarge x) = [MkSet D.empty (fromIntegral i) | i <- bitAscList x] ++ D.toAscList xlarge

toDescList :: Set -> [Set]
toDescList (MkSet xlarge x) = D.toDescList xlarge ++ [MkSet D.empty (fromIntegral i) | i <- bitDescList x]

-- | Bijection from 'Set' to 'Natural'.
--
--   CAUTION: The result of this function can be very very large,
--   which means it can consume huge amount of memory.
--
--   Also, technically this function is partial, because it gives up constructing
--   a value of @Natural@ that is greater than 2^(2^63) - 1,
--   by failing to address a set bit within @Int@. But we can't care,
--   because these values require at least 2^55 B ≒ 36PB for each anyway.
toNatural :: Set -> Natural
toNatural (MkSet xlarge x) = foldl' (.|.) (fromIntegral x) (safeBit <$> D.toDescList xlarge)
  where
    safeBit y = case toIntegralSized (toNatural y) of
      Nothing -> error "too large element"
      Just n -> bit n

fromNatural :: Natural -> Set
fromNatural n =
  let nsmall = n .&. bitMask
      nlarge = n `xor` nsmall
      xlarge = D.fromDistinctAscList $ map (fromNatural . fromIntegral) (bitListN nlarge)
   in MkSet xlarge (fromIntegral nsmall)
  where
    bw = finiteBitSize (0 :: SmallNat) :: Int

    bitMask :: Natural
    bitMask = bit bw - 1

    bitListN 0 = []
    bitListN m = filter (testBit m) [bw .. naturalLog2 m + 1]

---- Bit-fiddling utilities

-- | Union of all indices of \'1\' bit.
--
--   E.g. @137 = 0x89@ has 0th, 3rd, and 7th bits set to 1.
--
--   > 0x89 = 0b10001001
--
--   Then, @'unionPositions' 137@ returns @0 .|. 3 .|. 7 = 7@.
--
--   Formally, @unionPositions@ is a unique function which satisfies the specifications below:
--
--   > unionPositions 0 == 0
--   > unionPositions (bit i) == (fromIntegral i :: Word64), where 0 <= i < 64
--   > unionPositions64 (x .|. y) == unionPositions64 x .|. unionPositions64 y
unionPositions64 :: Word64 -> Word64
unionPositions64 x = foldl' (.|.) 0 $ map (\(p, b) -> if x .&. p == 0 then 0 else b) bitPatterns

bitPatterns :: [(Word64, Word64)]
bitPatterns =
  [ (0xAAAA_AAAA_AAAA_AAAA, 1), -- 0xA = 0b1010
    (0xCCCC_CCCC_CCCC_CCCC, 2), -- 0xC = 0b1100
    (0xF0F0_F0F0_F0F0_F0F0, 4), -- 0xF = 0b1111
    (0xFF00_FF00_FF00_FF00, 8),
    (0xFFFF_0000_FFFF_0000, 16),
    (0xFFFF_FFFF_0000_0000, 32)
  ]
{-# INLINE bitPatterns #-}

bitAscList, bitDescList :: FiniteBits a => a -> [Int]
bitAscList a = filter (testBit a) [0 .. finiteBitSize a - 1]
bitDescList a = reverse $ bitAscList a

-- Printing out

-- Show using Ackermann's encoding
showAckermann :: Set -> String
showAckermann = ($ "") . go
  where
    go (MkSet xlarge x)
      | D.null xlarge = shows x
      | x == 0 = braces $ commaList (go <$> D.toAscList xlarge)
      | otherwise = shows x . ('∪' :) . braces (commaList (go <$> D.toAscList xlarge))

commaList :: [ShowS] -> ShowS
commaList ss = foldr (.) id (intersperse (", " ++) ss)

braces :: ShowS -> ShowS
braces ss = ('{' :) . ss . ('}' :)
