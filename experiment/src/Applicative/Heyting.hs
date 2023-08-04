{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
module Applicative.Heyting where

import Data.Monoid (Ap(..))
import Lattice
import Control.Monad (guard)

import Newtypes

data F x a = F x (x -> a)
  deriving (Functor)

instance Heyting x => Applicative (F x) where
  pure a = F top (const a)
  F x f <*> F y g = F (x /\ y) fg
    where
      fg t = f (t /\ y) $ g (t /\ (y `imp` x))

instance (Enum x, Bounded x, Eq x, Eq a) => Eq (F x a) where
  F x f == F y g = x == y && (f <$> allXs) == (g <$> allXs)
    where allXs = [minBound .. maxBound]

newtype B = B Bool
  deriving ( Show, Read, Eq, Ord
           , Enum, Bounded, Num, Real, Integral) via Two
  deriving ( HasTop, HasBottom, Join, Meet
           , Lattice, LatticeBounded, LatticeDistributive
           , Heyting, LatticeDiff, LatticeComplement, Boolean) via Bool

instance (Enum x, Bounded x, Show x, Show a) => Show (F x a) where
  showsPrec p (F x f) =
    showParen (p > 9) $ ("F " ++) . showsPrec 10 x . (" " ++) . showParen True (showsFn f)

showsFn :: (Enum x, Bounded x, Show x, Show y) => (x -> y) -> String -> String
showsFn f = ("\\case {" ++) . body . ("}" ++)
  where
    body = foldr (.) id $ drop 1 $ concatMap showsCase [minBound .. maxBound]
    showsCase x = [("; "++), shows x . (" -> " ++) . shows (f x)]

type FBB = Ap (F B) String
fbs :: [FBB]
fbs = Ap <$>
  [ F 0 (\case {0 -> "a"; _ -> "b"}),
    F 1 (\case {0 -> "A"; _ -> "B"})
  ]

propAssoc :: (Semigroup a, Eq a) => [a] -> [(a,a,a)]
propAssoc fs = do
  x <- fs
  y <- fs
  z <- fs
  guard $ (x <> y) <> z /= x <> (y <> z)
  pure (x,y,z)

propUnitL, propUnitR :: (Monoid a, Eq a) => [a] -> [a]
propUnitL fs = [ x | x <- fs, (mempty <> x) /= x ]
propUnitR fs = [ x | x <- fs, (x <> mempty) /= x ]

-- *
-- 
-- >>> fbs !! 1
-- Ap {getAp = F 1 (\case {0 -> "A"; 1 -> "B"})}
-- >>> (propUnitL fbs, propUnitR fbs, propAssoc fbs)
-- ([],[],[])

-- >>> [x,y] = fbs
-- >>> x <> y
-- Ap {getAp = F 0 (\case {0 -> "aA"; 1 -> "bA"})}
-- >>> y <> x
-- Ap {getAp = F 0 (\case {0 -> "Aa"; 1 -> "Ab"})}
-- >>> x <> x <> x
-- Ap {getAp = F 0 (\case {0 -> "aaa"; 1 -> "aab"})}

newtype Five = Five Int
  deriving ( Show, Read, Eq, Ord
           , Num, Real, Integral) via Int
  deriving ( HasTop, HasBottom, Join, Meet
           , Lattice, LatticeBounded, LatticeDistributive
           , Heyting, LatticeDiff) via (Ordered Five)

instance Enum Five where
  fromEnum (Five i) = i
  toEnum i | 0 <= i && i <= 4 = Five i
           | otherwise        = error "OOB"

instance Bounded Five where
  minBound = 0
  maxBound = 4

ffs :: [Ap (F Five) String]
ffs = Ap <$> [ F i (\j -> "[" ++ show i ++ " " ++ show j++"]") | i <- [0 .. 4] ]

-- >>> ffs !! 1
-- Ap {getAp = F 1 (\case {0 -> "[1 0]"; 1 -> "[1 1]"; 2 -> "[1 2]"; 3 -> "[1 3]"; 4 -> "[1 4]"})}
-- >>> (propUnitL ffs, propUnitR ffs, propAssoc ffs)
-- ([],[],[])
-- 
-- >>> let [x0,x1,x2,x3,x4] = ffs
-- >>> x2 <> x0 <> x4
-- Ap {getAp = F 0 (\case {0 -> "[2 0][0 0][4 0]"; 1 -> "[2 0][0 1][4 0]"; 2 -> "[2 0][0 2][4 0]"; 3 -> "[2 0][0 3][4 0]"; 4 -> "[2 0][0 4][4 0]"})}
-- >>> x0 <> x2 <> x4
-- Ap {getAp = F 0 (\case {0 -> "[0 0][2 0][4 0]"; 1 -> "[0 1][2 0][4 0]"; 2 -> "[0 2][2 0][4 0]"; 3 -> "[0 2][2 0][4 0]"; 4 -> "[0 2][2 0][4 0]"})}
-- >>> x4 <> x0 <> x2
-- Ap {getAp = F 0 (\case {0 -> "[4 0][0 0][2 0]"; 1 -> "[4 0][0 1][2 0]"; 2 -> "[4 0][0 2][2 0]"; 3 -> "[4 0][0 2][2 0]"; 4 -> "[4 0][0 2][2 0]"})}

data G x a = G x (x -> a)
  deriving (Functor)

instance (Enum x, Bounded x, Show x, Show a) => Show (G x a) where
  showsPrec p (G x f) =
    showParen (p > 9) $ ("G " ++) . showsPrec 10 x . (" " ++) . showParen True (showsFn f)

instance Heyting x => Applicative (G x) where
  pure a = G top (const a)
  G x f <*> G y g = G (x /\ y) fg
    where
      fg t = f ((x `imp` y) /\ t) $ g ((y `imp` x) /\ t)

instance (Enum x, Bounded x, Eq x, Eq a) => Eq (G x a) where
  G x f == G y g = x == y && (f <$> allXs) == (g <$> allXs)
    where allXs = [minBound .. maxBound]

gfs :: [Ap (G Five) String]
gfs = Ap <$> [ G i (\j -> "[" ++ show i ++ " " ++ show j ++ "]") | i <- [0 .. 4] ]

-- >>> gfs !! 1
-- Ap {getAp = G 1 (\case {0 -> "[1 0]"; 1 -> "[1 1]"; 2 -> "[1 2]"; 3 -> "[1 3]"; 4 -> "[1 4]"})}
-- >>> (propUnitL gfs, propUnitR gfs, propAssoc gfs)
-- ([],[],[])

-- >>> let [x0,x1,x2,x3,x4] = gfs
-- >>> x2 <> x4
-- Ap {getAp = G 2 (\case {0 -> "[2 0][4 0]"; 1 -> "[2 1][4 1]"; 2 -> "[2 2][4 4]"; 3 -> "[2 3][4 4]"; 4 -> "[2 4][4 4]"})}
-- >>> x0 <> x2 <> x4
-- Ap {getAp = G 0 (\case {0 -> "[0 0][2 4][4 4]"; 1 -> "[0 1][2 4][4 4]"; 2 -> "[0 2][2 4][4 4]"; 3 -> "[0 3][2 4][4 4]"; 4 -> "[0 4][2 4][4 4]"})}
-- >>> x4 <> x0 <> x2
-- Ap {getAp = G 0 (\case {0 -> "[4 4][0 0][2 4]"; 1 -> "[4 4][0 1][2 4]"; 2 -> "[4 4][0 2][2 4]"; 3 -> "[4 4][0 3][2 4]"; 4 -> "[4 4][0 4][2 4]"})}
