{-# LANGUAGE TypeOperators #-}
module Data.PureSet.Class(
  SetModel(..),
  pair, matchPair, cartesianProduct,
  vnsucc, vnnat,
  
  IsList(..),
  defaultShowsPrec,
  showBrackets,
) where

import Prelude hiding (null)
import qualified Data.Foldable as F

import GHC.IsList
import Data.List (intersperse)
import Numeric.Natural (Natural)

-- | 
--
--  * @fromList (xs ++ xs) == fromList xs@
--  * @fromList (xs ++ ys) == fromList (ys ++ xs)@
--  * @fromList . toList == id@
class (Ord s, IsList s, Item s ~ s) => SetModel s where
  {-# MINIMAL #-}
  null :: s -> Bool
  null = F.null . toList
  
  size :: s -> Int
  size = F.length . toList
  
  member :: s -> s -> Bool
  member x y = F.elem x (toList y)
  
  isSubsetOf :: s -> s -> Bool
  isSubsetOf x y = union x y == y
  
  isProperSubsetOf :: s -> s -> Bool
  isProperSubsetOf x y = x /= y && isSubsetOf x y

  empty :: s
  empty = fromList []
  
  singleton :: s -> s
  singleton x = fromList [x]

  doubleton :: s -> s -> s
  doubleton x y = fromList [x, y]
  
  bigUnion :: s -> s
  bigUnion = fromList . concatMap toList . toList

  smap :: (s -> s) -> s -> s
  smap f = fromList . map f . toList
  
  sfilter :: (s -> Bool) -> s -> s
  sfilter f = fromList . filter f . toList

  union :: s -> s -> s
  union x y = bigUnion (doubleton x y)
  
  intersection :: s -> s -> s
  intersection x y = sfilter (member y) x

  difference :: s -> s -> s
  difference x y = sfilter (not . member y) x

  symdiff :: s -> s -> s
  symdiff x y = fromList $ filter (not . member x) (toList y) ++ filter (not . member y) (toList x)

  insert :: s -> s -> s
  insert x = union (singleton x)

  delete :: s -> s -> s
  delete x y = difference y (singleton x)

pair :: SetModel s => s -> s -> s
pair x y = doubleton (singleton x) (doubleton x y)

matchPair :: SetModel s => s -> Maybe (s,s)
matchPair xss = case toList xss of
  [xs] -> case toList xs of
    [x] -> Just (x,x)
    _ -> Nothing
  [ys, zs] -> case (toList ys, toList zs) of
    ([y1, y2], [z]) | y1 == z -> Just (y1, y2)
                    | y2 == z -> Just (y2, y1)
    ([y], [z1, z2]) | y == z1 -> Just (z1, z2)
                    | y == z2 -> Just (z2, z1)
    _ -> Nothing
  _ -> Nothing

cartesianProduct :: SetModel s => s -> s -> s
cartesianProduct xs ys = fromList [ pair x y | x <- toList xs, y <- toList ys ]

-- | successor function of von Neumann encoding of natural number
vnsucc :: SetModel s => s -> s
vnsucc x = insert x x

-- | von Neumann encoding of natural number
vnnat :: SetModel s => Natural -> s
vnnat 0 = empty
vnnat n = vnsucc (vnnat (n - 1))


-- Printing out

defaultShowsPrec :: SetModel s => Int -> s -> ShowS
defaultShowsPrec _ = showsBrackets

showsBrackets :: SetModel s => s -> ShowS
showsBrackets = go
  where
    go xs = brackets $ commaList (go <$> toList xs)
    brackets ss = ('[' :) . ss . (']' :)

showBrackets :: SetModel s => s -> String
showBrackets = ($ "") . showsBrackets

commaList :: [ShowS] -> ShowS
commaList ss = foldr (.) id (intersperse (", " ++) ss)
