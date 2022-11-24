{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hereditarily finite set
module Data.PureSet.Compact
  ( Set (),
    null,
    size,
    member,
    empty,
    singleton,
    insert,
    delete,
    union,
    bigUnion,
    intersection,
    difference,
    symdiff,
    toAscList,
    toDescList,
    fromList,
    fromAscList,
    fromDescList,
    toNatural,
    fromNatural,
    showBrackets,
    showBraces,
    showAckermann,
    pair,
    matchPair,
    cartesianProduct,
  )
where

import Data.Bits
import Data.List (foldl', intersperse)
import Data.Maybe (isNothing)
import qualified Data.Set as D
import qualified Data.Set.Extra as D
import Data.Word (Word64)
import qualified GHC.Exts as Ext
import Math.NumberTheory.Logarithms (naturalLog2)
import Numeric.Natural (Natural)
import Prelude hiding (null)

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
  showsPrec _ = showsBrackets

----

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

toAscList :: Set -> [Set]
toAscList (MkSet xlarge x) = [MkSet D.empty (fromIntegral i) | i <- bitAscList x] ++ D.toAscList xlarge

toDescList :: Set -> [Set]
toDescList (MkSet xlarge x) = D.toDescList xlarge ++ [MkSet D.empty (fromIntegral i) | i <- bitDescList x]

fromList :: [Set] -> Set
fromList = foldl' (flip insert) empty

fromAscList :: [Set] -> Set
fromAscList xs = case spanJust matchSmall xs of
  (smalls, larges) -> MkSet (D.fromAscList larges) (fromBitList smalls)

spanJust :: (a -> Maybe b) -> [a] -> ([b], [a])
spanJust f = go
  where
    go [] = ([], [])
    go (a : as) = case f a of
      Nothing -> ([], a : as)
      Just b -> case go as of
        ~(justs, nothings) -> (b : justs, nothings)

fromDescList :: [Set] -> Set
fromDescList xs = case span (isNothing . matchSmall) xs of
  (larges, smalls) -> case traverse matchSmall smalls of
    Just smalls' -> MkSet (D.fromDescList larges) (fromBitList smalls')
    Nothing -> error "Not a descending list?"

instance Ext.IsList Set where
  type Item Set = Set

  fromList = Data.PureSet.Compact.fromList
  toList = Data.PureSet.Compact.toAscList

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
bitDescList a = filter (testBit a) [n, n - 1 .. 0]
  where
    n = finiteBitSize a

fromBitList :: Bits a => [Int] -> a
fromBitList = foldl' (.|.) zeroBits . map bit

-- Printing out

showsBrackets :: Set -> ShowS
showsBrackets = go
  where
    go xs = brackets $ commaList (go <$> toAscList xs)

showBrackets :: Set -> String
showBrackets = ($ "") . showsBrackets

showBraces :: Set -> String
showBraces = ($ "") . go
  where
    go xs = braces $ commaList (go <$> toAscList xs)

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

brackets :: ShowS -> ShowS
brackets ss = ('[' :) . ss . (']' :)

--

-- | pair x y = {{x}, {x,y}}
pair :: Set -> Set -> Set
pair x y = fromList [sx, sx `union` sy]
  where
    sx = singleton x -- {x}
    sy = singleton y -- {y}

-- | If a given set can be constructed by 'pair', return the original values of the pair.
matchPair :: Set -> Maybe (Set, Set)
matchPair z = case toAscList z of
  -- If @x == y@, then @pair x y == singleton (singleton x)@
  [sx] -> case toAscList sx of
    [x] -> Just (x, x)
    _ -> Nothing
  -- It's always true that @x <= x `union` y@ for @x /= y@.
  -- Therefore we can assume the smallest element is singleton and
  -- the next element is doubleton.
  [sx, sxy] -> case (toAscList sx, toAscList sxy) of
    ([x], [t, u])
      | x == t -> Just (x, u)
      | x == u -> Just (x, t)
    _ -> Nothing
  _ -> Nothing

cartesianProduct :: Set -> Set -> Set
cartesianProduct xs ys
  | size xs <= size ys = foldl' union empty [fromAscList [pair x y | y <- toAscList ys] | x <- toAscList xs]
  | otherwise = foldl' union empty [fromAscList [pair x y | x <- toAscList xs] | y <- toAscList ys]
