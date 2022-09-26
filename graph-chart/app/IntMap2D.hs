{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}
module IntMap2D where

import GHC.Exts

import Data.IntMap.Strict qualified as IM
import Data.IntMap.Strict (IntMap)

import Data.Bits
import GHC.Word
import Data.WideWord.Word128

data IntMap2D a = MkIntMap2D (IntMap (IntMap a))
  deriving (Eq, Ord)

-- !!! This module assumes Word = 64 bit width unsigned integer !!!

toKey :: Int -> Int -> Word128
toKey x y = wordInterleave64 (bias x) (bias y)

fromKey :: Word128 -> (Int, Int)
fromKey k = case wordUnInterleave64 k of
  (x, y) -> (unbias x, unbias y)

data Tile = Tile !Word128 !Word128
  deriving (Show, Eq, Ord)

tileBoundingBox :: Tile -> ((Int, Int), (Int, Int))
tileBoundingBox (Tile key mask) = (fromKey key, fromKey (key .|. complement mask))

entireTile :: Tile
entireTile = Tile 0 0

atomTile :: Int -> Int -> Tile
atomTile x y = Tile (toKey x y) (complement zeroBits)

-- | Make a bitmask for the common prefix of two bit-represented integers.
-- 
-- 
-- Example:
-- 
-- >>> matchingPrefixMask 0b0011_0011 0b0011_0011 == (0b1111_1111 :: Word8)
-- True
-- >>> matchingPrefixMask 0b0011_0011 0b0000_0011 == (0b1100_0000 :: Word8)
-- True
-- >>> matchingPrefixMask 0b0011_0011 0b1111_0011 == (0b0000_0000 :: Word8)
-- True
matchingPrefixMask :: (FiniteBits a, Num a) => a -> a -> a
matchingPrefixMask x y = complement (bit (finiteBitSize x - countLeadingZeros (xor x y))) + 1

instance Semigroup Tile where
  Tile k1 mask1 <> Tile k2 mask2 = Tile k mask
    where mask = mask1 .&. mask2 .&. matchingPrefixMask k1 k2
          k = k1 .&. mask --  == k2 .&. mask

lookup :: Int -> Int -> IntMap2D a -> Maybe a
lookup x y = lookupByKey (toKey x y)

lookupByKey :: Word128 -> IntMap2D a -> Maybe a
lookupByKey (Word128 hi lo) (MkIntMap2D mm) = IM.lookup (unbias hi) mm >>= IM.lookup (unbias lo)

sliceIntMap :: Int -> Int -> IntMap a -> IntMap a
sliceIntMap from to = takeGT from . takeLT to
  where
    takeLT, takeGT :: Int -> IntMap a -> IntMap a
    takeLT n | n == maxBound = id
             | otherwise     = fst . IM.split (succ n)
    takeGT n | n == minBound = id
             | otherwise     = snd . IM.split (pred n)

restrict :: Tile -> IntMap2D a -> IntMap2D a
restrict (Tile (Word128 keyHi keyLo) (Word128 maskHi maskLo)) (MkIntMap2D mm)
  | maskLo == 0 = MkIntMap2D $ sliceIntMap (unbias keyHi) (unbias (keyHi .|. complement maskHi)) mm
  | otherwise {- maskHi = 0b1111...111 -} 
      = case IM.lookup (unbias keyHi) mm of
          Nothing -> MkIntMap2D IM.empty
          Just m  -> let m' = sliceIntMap (unbias keyLo) (unbias (keyLo .|. complement maskLo)) m
                     in MkIntMap2D $ IM.singleton (unbias keyHi) m'

-- Biased cast, order preserved
bias :: Int -> Word64
bias (I# x) = W64# (xor# 0x8000_0000_0000_0000## (int2Word# x))

-- Biased cast, order preserved
unbias :: Word64 -> Int
unbias (W64# x) = I# (word2Int# (xor# 0x8000_0000_0000_0000## x))

----

wordInterleave64 :: Word64 -> Word64 -> Word128
wordInterleave64 (W64# x) (W64# y) = Word128 (W64# (wordInterleave32# xh yh)) (W64# (wordInterleave32# xl yl))
  where xh = uncheckedShiftRL64# x 32#
        xl = and# 0x0000_0000_FFFF_FFFF## x
        yh = uncheckedShiftRL64# y 32#
        yl = and# 0x0000_0000_FFFF_FFFF## y

wordInterleave32# :: Word# -> Word# -> Word#
wordInterleave32# x y = or# (pdep# x bitMaskX) (pdep# y bitMaskY)
  where
    bitMaskX = 0xAAAA_AAAA_AAAA_AAAA##
    bitMaskY = not# bitMaskX

wordUnInterleave64 :: Word128 -> (Word64, Word64)
wordUnInterleave64 (Word128 (W64# hi) (W64# lo)) = (W64# x, W64# y)
  where
    !(# xh, yh #) = wordUnInterleave32# hi
    !(# xl, yl #) = wordUnInterleave32# lo
    !x = or# xl (uncheckedShiftL# xh 32#)
    !y = or# yl (uncheckedShiftL# yh 32#)

wordUnInterleave32# :: Word# -> (# Word#, Word# #)
wordUnInterleave32# xy = (# pext# xy bitMaskX, pext# xy bitMaskY #)
  where
    bitMaskX = 0xAAAA_AAAA_AAAA_AAAA##
    bitMaskY = not# bitMaskX
