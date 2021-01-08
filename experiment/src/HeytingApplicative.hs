{-# LANGUAGE DeriveFunctor #-}
module HeytingApplicative where

import Data.Word (Word8)
import qualified Data.Set as Set

-- | Mystery applicative
newtype H a = H (Bool, Bool -> a)
  deriving Functor

instance Applicative H where
  pure a = H (True, const a)
  H (x, f) <*> H (y, g) = H (x && y, fg)
    where fg t = f (t && (x ===> y)) (g (t && x))

-- | "x implies y" operator
(===>) :: Bool -> Bool -> Bool
x ===> y = not x || y

-- | Heyting algebra-based applicative: linear order edition
newtype Hord x a = Hord (x, x -> a)
  deriving (Functor)

instance (Ord x, Bounded x) => Applicative (Hord x) where
  pure a = Hord (maxBound, const a)
  Hord (x, f) <*> Hord (y, g) = Hord (min x y, fg)
    where x_to_y | x <= y    = maxBound
                 | otherwise = y
          fg t = f (min t x_to_y) (g (min t x))

testHord :: Hord Word8 [Word8]
testHord = sequenceA [ Hord (n, id) | n <- ns ]
  where ns = [1,2,1,3,1,4,1,5,1,6,1,7]

-- | Heyting algebra of cofinite sets
data Cofin u = Empty | NotIn !(Set.Set u)
  deriving (Eq, Show)

member :: Ord u => u -> Cofin u -> Bool
member _ Empty = False
member u (NotIn s) = u `Set.notMember` s

-- forall a. a `member` full
full :: Cofin u
full = NotIn Set.empty

-- forall a x y.
--   a `member` intersection x y == (a `member` x && a `member` y) 
intersection :: Ord u => Cofin u -> Cofin u -> Cofin u
intersection (NotIn s) (NotIn t) = NotIn (Set.union s t)
intersection _ _ = Empty

-- forall a x y.
--   a `member` impCofin x y == (a `member` x ===> a `member` y) 
impCofin :: Ord u => Cofin u -> Cofin u -> Cofin u
impCofin Empty _ = full
impCofin _ Empty = Empty
impCofin (NotIn s) (NotIn t) = NotIn (t Set.\\ s)

-- | Heyting algebra-based applicative: cofinite set edition
newtype HCofin u a = HCofin (Cofin u, Cofin u -> a)
  deriving Functor

instance Ord u => Applicative (HCofin u) where
  pure a = HCofin (full, const a)
  HCofin (x,f) <*> HCofin (y,g) = HCofin (intersection x y, fg)
    where
      fg t = f (t `intersection` (x `impCofin` y)) (g (t `intersection` x))

