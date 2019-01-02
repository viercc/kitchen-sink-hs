{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
module Matrix(
  AdditiveGroup(..),
  Ring(..),

  Matrix(..),
  generateMat,
  zeroMat, oneMat, eyeMat,

  multMatBy, multMat, multBlockMat
) where

import           Prelude             hiding (fromInteger, negate)
import qualified Prelude             as P

import           Control.Applicative
import           Data.Ratio

import           Data.List           (foldl', transpose)
import           Data.Proxy

import           Data.Kind
import           GHC.TypeLits

class AdditiveGroup a where
  plus :: a -> a -> a
  default plus :: (Num a) => a -> a -> a
  plus = (+)

  zero :: a
  default zero :: (Num a) => a
  zero = 0

  negate :: a -> a
  default negate :: (Num a) => a -> a
  negate = P.negate

  gtimes :: Integer -> a -> a
  default gtimes :: (Num a) => Integer -> a -> a
  gtimes n a = P.fromInteger n * a

instance AdditiveGroup Int
instance AdditiveGroup Integer
instance (Integral a) => AdditiveGroup (Ratio a)
instance AdditiveGroup Float
instance AdditiveGroup Double

class (AdditiveGroup a) => Ring a where
  mult :: a -> a -> a
  default mult :: (Num a) => a -> a -> a
  mult = (*)
  
  one :: a
  default one :: (Num a) => a
  one = 1
  
  fromInteger :: Integer -> a
  default fromInteger :: (Num a) => Integer -> a
  fromInteger = P.fromInteger

instance Ring Int
instance Ring Integer
instance (Integral a) => Ring (Ratio a)
instance Ring Float
instance Ring Double

-- There can be another implementation, but here I use this
newtype Matrix (m :: Nat) (n :: Nat) (k :: Type) = Matrix [[k]]
    deriving (Show, Eq, Functor)

instance (KnownNat m, KnownNat n) => Applicative (Matrix m n) where
  pure x = withShape $ \m n -> Matrix $
    replicate (fromInteger m) (replicate (fromInteger n) x)

  liftA2 f (Matrix as) (Matrix bs) = Matrix $ zipWith (zipWith f) as bs

instance (KnownNat m, KnownNat n, AdditiveGroup k) => AdditiveGroup (Matrix m n k) where
  plus = liftA2 plus
  zero = pure zero
  negate = fmap negate
  gtimes n = fmap (gtimes n)


generateMat :: forall m n k. (KnownNat n, KnownNat m) =>
               (Integer -> Integer -> k) -> Matrix m n k
generateMat f = withShape $ \m n -> Matrix
  [ [ f i j | j <- [1..n] ] | i <- [1..m] ]

zeroMat :: forall m n k. (KnownNat n, KnownNat m, AdditiveGroup k) => Matrix m n k
zeroMat = zero

oneMat :: forall m n k. (KnownNat n, KnownNat m, Ring k) => Matrix m n k
oneMat = pure one

eyeMat :: forall m n k. (KnownNat n, KnownNat m, Ring k) => Matrix m n k
eyeMat = generateMat delta
  where delta i j = if i == j then one else zero



multMatBy :: (AdditiveGroup z) => (x -> y -> z) ->
             Matrix m p x -> Matrix p n y -> Matrix m n z
multMatBy mult' (Matrix as) (Matrix bs) =
  Matrix [ foldl' plus zero . zipWith mult' v1 <$> transpose bs |  v1 <- as ]

multMat :: (Ring k) => Matrix m p k -> Matrix p n k -> Matrix m n k
multMat = multMatBy mult

multBlockMat :: (Ring k, KnownNat m2, KnownNat n2) =>
                Matrix m1 p1 (Matrix m2 p2 k) ->
                Matrix p1 n1 (Matrix p2 n2 k) ->
                Matrix m1 n1 (Matrix m2 n2 k)
multBlockMat = multMatBy multMat

----------------------------------------

withShape :: forall m n k. (KnownNat m, KnownNat n) =>
             (Integer -> Integer -> Matrix m n k) -> Matrix m n k
withShape f = f (natVal (Proxy @m)) (natVal (Proxy @n))
