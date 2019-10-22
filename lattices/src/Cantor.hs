{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes        #-}
module Cantor where

import           Control.Applicative
import           Control.Arrow       ((***))
import           Data.Foldable       (toList)
import           Numeric.Interval

import           Searchable

data Stream a = Stream a (Stream a)
              deriving (Show, Functor, Foldable, Traversable)

instance Applicative Stream where
  pure a = let as = Stream a as in as
  (Stream f fs) <*> (Stream x xs) = Stream (f x) (fs <*> xs)

streamOf :: Set a -> Set (Stream a)
streamOf xs = Stream <$> xs <*> streamOf xs

type Cantor = Stream Bool
cantor :: Set Cantor
cantor = streamOf bit

type QInterval = Interval Rational

newtype RealNum = RealNum { unReal :: Stream QInterval }

instance Eq RealNum where
  (==) = error "Equality on RealNum is undecidable"

eventually :: (forall a. (Ord a) => a -> a -> Bool) -> RealNum -> RealNum -> Bool
eventually rel (RealNum x) (RealNum y) = loop x y
  where
    notRel :: Ord a => a -> a -> Bool
    notRel = \p q -> not (rel p q)
    loop (Stream x0 x') (Stream y0 y') =
      case (certainly rel x0 y0, certainly notRel x0 y0) of
        (True, _)      -> True
        (False, True)  -> False
        (False, False) -> loop x' y'

instance Ord RealNum where
  x < y = eventually (<) x y
  x > y = eventually (>) x y
  x <= y = not (x > y)
  x >= y = not (x < y)

liftReal1 :: (forall a. Fractional a => a -> a) -> RealNum -> RealNum
liftReal1 op x = RealNum $ fmap op (unReal x)

liftReal2 :: (forall a. Fractional a => a -> a -> a) -> RealNum -> RealNum -> RealNum
liftReal2 op x y = RealNum $ liftA2 op (unReal x) (unReal y)

instance Num RealNum where
  fromInteger n = fromRational (fromInteger n)
  (+) = liftReal2 (+)
  (-) = liftReal2 (-)
  (*) = liftReal2 (*)
  negate = liftReal1 negate
  abs    = liftReal1 abs
  signum = liftReal1 signum

instance Fractional RealNum where
  fromRational x = RealNum $ pure (Numeric.Interval.singleton x)
  (/) = liftReal2 (/)

cantorToReal :: Cantor -> RealNum
cantorToReal = RealNum . loop 0 1
  where
    loop x0 step (Stream b x') =
      let step' = step/3
          x1 = x0 + (if b then step'*2 else 0)
      in Stream (x0 ... x0 + step) (loop x1 step' x')

realToDouble :: RealNum -> Double
realToDouble (RealNum x) =
  let doubles = (fromRational . midpoint) <$> toList x
      converged (x1,x2) = x1 == x2
      (goal, _) = head $ dropWhile (not.converged) $ zip doubles (tail doubles)
  in goal

cantorToDouble :: Cantor -> Double
cantorToDouble = realToDouble . cantorToReal

-- | Find x in Cantor set where 1/2 < x^2 < 3/4
example1 :: Maybe Double
example1 = cantorToDouble <$> search cantor condition
  where condition x = let y = cantorToReal x ^ (2 :: Int)
                      in (1/2 < y) && (y < 3/4)

-- | Find x in Cantor set where 3 < (1+x)^3 < 4
example2 :: Maybe Double
example2 = cantorToDouble <$> search cantor condition
  where condition x = let y = (cantorToReal x + 1) ^ (3::Int)
                      in (3 < y) && (y < 4)

-- | Find (x,y) in Cantor^2 where 1/2 - eps < x + y <= 1/2
example3 :: Maybe (Double, Double)
example3 = (cantorToDouble *** cantorToDouble) <$> search (cantor `prod` cantor) condition
  where eps = (1/2) ^ (10 :: Int) :: RealNum
        condition (x,y) = let z = cantorToReal x + cantorToReal y
                          in (1/2 - eps < z) && (z <= 1/2)
