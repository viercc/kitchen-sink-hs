{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
module HeytingApplicative where

import Data.Word (Word8)
import Lattice
import Data.Function (on)
import Control.Applicative
import Data.Bool (bool)
import Control.Monad (guard)

data F x a = F x (x -> a)
  deriving (Functor)

instance Heyting x => Applicative (F x) where
  pure a = F top (const a)
  F x f <*> F y g = F (x /\ y) fg
    where
      fg t = f (t /\ (x `imp` y)) $ g (x `imp` t)

data B = O | I
  deriving (Show, Read, Eq, Ord, Enum, Bounded)

type FBB = F Bool [B]
fbs :: [FBB]
fbs = [F True r, F False r]
  where
    r = pure . bool O I

fbrep :: F Bool c -> (Bool, c, c)
fbrep (F x f) = (x, f True, f False)

fbeq :: (Eq a) => F Bool a -> F Bool a -> Bool
fbeq = (==) `on` fbrep

(<++>) :: Applicative f => f [a] -> f [a] -> f [a]
(<++>) = liftA2 (++)

propUnitL, propUnitR :: [FBB]
propUnitL = [ x | x <- fbs, not $ (pure [] <++> x) `fbeq` x ]
propUnitR = [ x | x <- fbs, not $ (x <++> pure []) `fbeq` x ]

propAssoc :: [(FBB,FBB,FBB)]
propAssoc = do
  x <- fbs
  y <- fbs
  z <- fbs
  guard $ not $ ((x <++> y) <++> z) `fbeq` (x <++> (y <++> z))
  pure (x,y,z)

testFord :: F (Ordered Word8) [Word8]
testFord = traverse i [1,2,1,3,1,4,1,5,1,6,1,7]
  where i n = F (Ordered n) getOrdered

data H x a = H x (x -> a)
  deriving (Functor)

instance Heyting x => Applicative (H x) where
  pure a = H top (const a)
  H x f <*> H y g = H (x /\ y) fg
    where fg t = f (t /\ (x `imp` y)) (g (t /\ x))

testHord :: H (Ordered Word8) [Word8]
testHord = traverse i [1,2,1,3,1,4,1,5,1,6,1,7]
  where i n = H (Ordered n) getOrdered
