{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hereditarily finite set
module Data.PureSet
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
    nextSet,
    showBrackets,
    showBraces,
    showAngles,
    pair,
    matchPair,
    cartesianProduct,
    vnsucc,
    vnnat,
    depth,
  )
where

import Data.Bits
import Data.List (foldl', intersperse)
import qualified Data.Set as D
import qualified Data.Set.Extra as D
import qualified GHC.Exts as Ext
import Math.NumberTheory.Logarithms (naturalLog2)
import Numeric.Natural (Natural)
import Prelude hiding (null)

newtype Set = MkSet (D.Set Set)
  deriving (Eq)

-- | The order which does not changed by bijections 'toNatural' and 'fromNatural'
instance Ord Set where
  compare (MkSet x) (MkSet y) = compare (D.toDescList x) (D.toDescList y)

instance Show Set where
  showsPrec _ = showsBrackets

----

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

-- | insert x y = union (singleton x) y
insert :: Set -> Set -> Set
insert x (MkSet y) = MkSet (D.insert x y)

-- | delete x y = difference y (singleton x)
delete :: Set -> Set -> Set
delete x (MkSet y) = MkSet (D.delete x y)

union :: Set -> Set -> Set
union (MkSet x) (MkSet y) = MkSet (D.union x y)

bigUnion :: Set -> Set
bigUnion (MkSet x) = D.foldl' union empty x

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

fromList :: [Set] -> Set
fromList = foldl' (flip insert) empty

fromAscList :: [Set] -> Set
fromAscList xs = MkSet (D.fromAscList xs)

fromDescList :: [Set] -> Set
fromDescList xs = MkSet (D.fromDescList xs)

instance Ext.IsList Set where
  type Item Set = Set

  fromList = Data.PureSet.fromList
  toList = Data.PureSet.toAscList

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

-- Printing out

showsBrackets :: Set -> ShowS
showsBrackets = go
  where
    go xs = brackets $ commaList (go <$> toAscList xs)
    brackets ss = ('[' :) . ss . (']' :)

showBrackets :: Set -> String
showBrackets = ($ "") . showsBrackets

showBraces :: Set -> String
showBraces = ($ "") . go
  where
    braces ss = ('{' :) . ss . ('}' :)
    go xs = braces $ commaList (go <$> toAscList xs)

commaList :: [ShowS] -> ShowS
commaList ss = foldr (.) id (intersperse (", " ++) ss)

showAngles :: Set -> String
showAngles = ($ "") . go
  where
    angles ss = ('<' :) . ss . ('>' :)
    go xs = angles $ foldr (.) id (go <$> toAscList xs)

--

-- | successor function of von Neumann encoding of natural number
vnsucc :: Set -> Set
vnsucc x@(MkSet s) = MkSet (D.insert x s)

-- | von Neumann encoding of natural number
vnnat :: Natural -> Set
vnnat 0 = empty
vnnat n = vnsucc (vnnat (n - 1))

-- | Depth of a set @x@. Length @n@ of the longest chain below.
--
--   > empty = x0 ∈ x1 && x1 ∈ x2 && x2 ∈ ... ∈ xn = x
depth :: Set -> Natural
depth = loop 0
  where
    loop !n (MkSet s) = case D.lookupMax s of
      Nothing -> n
      Just s' -> loop (1 + n) s'

-- | pair x y = {{x}, {x,y}}
pair :: Set -> Set -> Set
pair x y = case compare x y of
  LT -> mk [mk [x], mk [x, y]]
  EQ -> mk [mk [x]]
  GT -> mk [mk [x], mk [y, x]]
  where
    -- unsafe make
    mk = MkSet . D.fromDistinctAscList

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
