{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
module HeytingApplicative where

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
-- >>> fbs
-- [Ap {getAp = F 0 (\case {0 -> "a"; 1 -> "b"})},Ap {getAp = F 1 (\case {0 -> "A"; 1 -> "B"})}]

-- >>> let [x,y] = fbs in x <> y
-- Ap {getAp = F 0 (\case {0 -> "aA"; 1 -> "bA"})}
-- >>> let [x,y] = fbs in y <> x
-- Ap {getAp = F 0 (\case {0 -> "Aa"; 1 -> "Ab"})}
-- >>> let [x,y] = fbs in x <> x <> x
-- Ap {getAp = F 0 (\case {0 -> "aaa"; 1 -> "aab"})}

-- >>> propAssoc fbs
-- []

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
ffs = Ap <$> [ F i show | i <- [0 .. 4] ]

-- *
-- 
-- >>> let [x0,x1,x2,x3,x4] = ffs
-- >>> x2 <> x0 <> x4
-- Ap {getAp = F 0 (\case {0 -> "000"; 1 -> "010"; 2 -> "020"; 3 -> "030"; 4 -> "040"})}

-- >>> let [x0,x1,x2,x3,x4] = ffs
-- >>> x0 <> x2 <> x4
-- Ap {getAp = F 0 (\case {0 -> "000"; 1 -> "100"; 2 -> "200"; 3 -> "200"; 4 -> "200"})}

-- >>> let [x0,x1,x2,x3,x4] = ffs
-- >>> x4 <> x0 <> x2
-- Ap {getAp = F 0 (\case {0 -> "000"; 1 -> "010"; 2 -> "020"; 3 -> "020"; 4 -> "020"})}
