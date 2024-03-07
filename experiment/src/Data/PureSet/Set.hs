{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}

-- | Hereditarily finite set
module Data.PureSet.Set
  ( Set (),
    toAscList, toDescList,
    toNatural, fromNatural, nextSet,

    depth
  )
where

import Data.Bits
import Data.List (foldl')
import qualified Data.Set as D
import qualified Data.Set.Extra as D

import Math.NumberTheory.Logarithms (naturalLog2)
import Numeric.Natural (Natural)
import Prelude hiding (null)

import Data.PureSet.Class

newtype Set = MkSet (D.Set Set)
  deriving (Eq)

-- | The order which does not changed by bijections 'toNatural' and 'fromNatural'
instance Ord Set where
  compare (MkSet x) (MkSet y) = compare (D.toDescList x) (D.toDescList y)

instance Show Set where
  showsPrec = defaultShowsPrec

instance IsList Set where
  type Item Set = Set

  fromList :: [Set] -> Set
  fromList = foldl' (flip insert) empty

  toList :: Set -> [Set]
  toList = toAscList


instance SetModel Set where
  null :: Set -> Bool
  null (MkSet x) = D.null x

  size :: Set -> Int
  size (MkSet x) = D.size x

  member :: Set -> Set -> Bool
  member x (MkSet y) = D.member x y

  empty :: Set
  empty = MkSet D.empty

  singleton :: Set -> Set
  singleton x = MkSet (D.singleton x)

  union :: Set -> Set -> Set
  union (MkSet x) (MkSet y) = MkSet (D.union x y)

  bigUnion :: Set -> Set
  bigUnion (MkSet x) = D.foldl' union empty x

  smap :: (Set -> Set) -> Set -> Set
  smap f (MkSet x) = MkSet $ D.map f x

  sfilter :: (Set -> Bool) -> Set -> Set
  sfilter f (MkSet x) = MkSet $ D.filter f x

  intersection :: Set -> Set -> Set
  intersection (MkSet x) (MkSet y) = MkSet (D.intersection x y)

  difference :: Set -> Set -> Set
  difference (MkSet x) (MkSet y) = MkSet (D.difference x y)

  symdiff :: Set -> Set -> Set
  symdiff (MkSet x) (MkSet y) = MkSet (D.symdiff x y)

toAscList :: Set -> [Set]
toAscList (MkSet x) = D.toAscList x

toDescList :: Set -> [Set]
toDescList (MkSet x) = D.toDescList x

-- | Bijection from 'Natural' to 'Set'.
toNatural :: Set -> Natural
toNatural (MkSet x) = foldl' (.|.) 0 (safeBit <$> D.toDescList x)
  where
    safeBit y = case toIntegralSized (toNatural y) of
      Nothing -> error "too large element"
      Just n -> bit n

-- | Bijection from 'Natural' to 'Set'.
fromNatural :: Natural -> Set
fromNatural n =
  MkSet $
    D.fromDistinctAscList $
      map (fromNatural . fromIntegral) (bitListN n)

bitListN :: Natural -> [Int]
bitListN 0 = []
bitListN m = filter (testBit m) [0 .. naturalLog2 m + 1]

-- @nextSet = fromNatural . succ . toNatural@ but without actually making (possibly big) intermediate @Natural@.
nextSet :: Set -> Set
nextSet = loop empty
  where
    loop x (MkSet ys) = case D.minView ys of
      Nothing -> singleton x
      Just (y, ys')
        | x == y -> loop (nextSet x) (MkSet ys')
        | otherwise -> MkSet $ D.insert x (D.insert y ys')

--

-- | Depth of a set @x@. Length @n@ of the longest chain below.
--
--   > empty = x0 ∈ x1 && x1 ∈ x2 && x2 ∈ ... ∈ xn = x
depth :: Set -> Natural
depth = loop 0
  where
    loop !n (MkSet s) = case D.lookupMax s of
      Nothing -> n
      Just s' -> loop (1 + n) s'
