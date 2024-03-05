module Data.FiniteSet where

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.Ordered as OL
import Numeric.Natural (Natural)
import Prelude hiding (succ)

-- | Invariant: @toList xs@ is sorted in descending order
data Set = Empty | Set :> Set
  deriving (Eq, Ord)

infixr 3 :>

instance Show Set where
  showsPrec _ Empty = ("0" ++)
  showsPrec _ (x :> xs) = braces $ sepBy comma (shows <$> (x :| toList xs))
    where
      braces ss = ("{" ++) . ss . ("}" ++)
      sepBy delimiter = go
        where
          go (s :| rest) = s . go' rest
          go' [] = id
          go' (s : rest) = delimiter . go (s :| rest)
      comma = ("," ++)

toList :: Set -> [Set]
toList Empty = []
toList (x :> xs) = x : toList xs

fromList :: [Set] -> Set
fromList = fromDistinctDescList . OL.nubSortBy descending

descending :: Ord a => a -> a -> Ordering
descending = flip compare

fromDistinctDescList :: [Set] -> Set
fromDistinctDescList = foldr (:>) Empty

singleton :: Set -> Set
singleton x = x :> Empty

doubleton :: Set -> Set -> Set
doubleton x y = case compare x y of
  LT -> y :> x :> Empty
  EQ -> x :> Empty
  GT -> x :> y :> Empty

succ :: Set -> Set
succ x = x :> x

nat :: Natural -> Set
nat 0 = Empty
nat n = succ (nat (n - 1))

union :: Set -> Set -> Set
union xs ys = fromDistinctDescList $ OL.unionBy descending (toList xs) (toList ys)

unions :: [Set] -> Set
unions = treefold union Empty

bigUnion :: Set -> Set
bigUnion = unions . toList

treefold :: (a -> a -> a) -> a -> [a] -> a
treefold op z = go
  where
    go [] = z
    go (x : xs) = treefoldNE op (x :| xs)

treefoldNE :: (a -> a -> a) -> NonEmpty a -> a
treefoldNE op = go
  where
    go (x :| []) = x
    go (x :| y : xs) = go (op x y :| pairs xs)

    pairs (x : y : xs') = op x y : pairs xs'
    pairs xs = xs

intersection :: Set -> Set -> Set
intersection xs ys = fromDistinctDescList $ OL.isectBy descending (toList xs) (toList ys)

intersections :: NonEmpty Set -> Set
intersections = treefoldNE intersection

minus :: Set -> Set -> Set
minus xs ys = fromDistinctDescList $ OL.minusBy descending (toList xs) (toList ys)

xunion :: Set -> Set -> Set
xunion xs ys = fromDistinctDescList $ OL.xunionBy descending (toList xs) (toList ys)

xunions :: [Set] -> Set
xunions = treefold xunion Empty