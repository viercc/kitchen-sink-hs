{-# OPTIONS_GHC -Wall #-}
module Heap where

import Prelude hiding (repeat, zipWith, (!!))
import Data.Bits

data Heap a = Heap a (Heap a) (Heap a)
  deriving (Show)

instance Functor Heap where
  fmap f = go
    where go (Heap a al ar) = Heap (f a) (go al) (go ar)

instance Applicative Heap where
  pure = repeat
  (<*>) = zipWith id
  (<*) = const
  (*>) = const id

instance Monad Heap where
  return = pure
  Heap a l r >>= f = Heap b l' r'
    where
      Heap b _  _  = f a
      Heap _ l' _  = l >>= f
      Heap _ _  r' = r >>= f

repeat :: a -> Heap a
repeat a = let as = Heap a as as in as

zipWith :: (a -> b -> c) -> Heap a -> Heap b -> Heap c
zipWith f = go
  where go (Heap a as1 as2) (Heap b bs1 bs2) =
          Heap (f a b) (go as1 bs1) (go as2 bs2)

genericIndex :: (Integral b, Bits b) => Heap a -> b -> a
genericIndex (Heap zero neg pos) n
  | n < 0     = at' neg (negate n)
  | n == 0    = zero
  | otherwise = at' pos n
  where
    at' (Heap a _ _) 1 = a
    at' (Heap _ l r) k =
      let next = if k .&. 1 == 0 then l else r
      in at' next (k `unsafeShiftR` 1)

(!!) :: Heap a -> Int -> a
(!!) = genericIndex

integerTable :: Heap Integer
integerTable = Heap 0 (fmap negate natTable) natTable

natTable :: Heap Integer
natTable = Heap 1 (fmap l natTable) (fmap r natTable)
  where
    l n = n `unsafeShiftL` 1
    r n = (n `unsafeShiftL` 1) .|. 1
