{-# LANGUAGE InstanceSigs #-}
module Math.QSqrt2 where

import Data.Ratio (denominator, numerator)

-- | Field ℚ(√2)
data QSqrt2 = MkQSqrt2 !Rational !Rational
  deriving (Eq)

sqrt2 :: QSqrt2
sqrt2 = MkQSqrt2 0 1

toDouble :: QSqrt2 -> Double
toDouble (MkQSqrt2 a b) = fromRational a + fromRational b * sqrt 2

prettyRational :: Rational -> ShowS
prettyRational x
  | denominator x == 1 = shows (numerator x)
  | otherwise          = shows (numerator x) . (" / " ++) . shows (denominator x)

instance Show QSqrt2 where
  showsPrec p (MkQSqrt2 a b)
    | a == 0, b == 0 = ("0" ++)
    | a == 0 = showParen (p > 7) $ prettyRational b . (" * sqrt2" ++)
    | b == 0 = showParen (p > 7) $ prettyRational a
    | otherwise = showParen (p > 6) $ prettyRational a . (" + " ++) . prettyRational b . (" * sqrt2" ++)

instance Ord QSqrt2 where
  compare (MkQSqrt2 a b) (MkQSqrt2 c d) = compare0 (MkQSqrt2 (a - c) (b - d))

-- (Can be optimized)
square :: Rational -> Rational
square x = x * x

-- compare (x + √2 * y)
compare0 :: QSqrt2 -> Ordering
compare0 (MkQSqrt2 x y)
  | x > 0, y < 0  = compare (square x) (2 * square y)
  | x <= 0, y < 0 = LT
  | y == 0        = compare x 0
  | x >= 0, y > 0 = GT
  | otherwise    = compare (2 * square y) (square x)
    -- x < 0, y < 0

instance Num QSqrt2 where
  fromInteger n = MkQSqrt2 (fromInteger n) 0

  MkQSqrt2 a b + MkQSqrt2 c d = MkQSqrt2 (a + c) (b + d)
  MkQSqrt2 a b - MkQSqrt2 c d = MkQSqrt2 (a - c) (b - d)
  MkQSqrt2 a b * MkQSqrt2 c d = MkQSqrt2 (a * c + 2 * b * d) (a * d + b * c)

  negate (MkQSqrt2 a b) = MkQSqrt2 (negate a) (negate b)
  abs x = if x < 0 then negate x else x
  signum x = case compare0 x of
    LT -> negate 1
    EQ -> 0
    GT -> 1

instance Fractional QSqrt2 where
  fromRational x = MkQSqrt2 x 0

  recip (MkQSqrt2 x y)
    | x == 0, y == 0 = error "division by zero"
    | otherwise      = MkQSqrt2 (x / r) (- y / r)
        where
          r = square x - 2 * square y
          -- It is guaranteed that r /= 0

-- Find an approximation of √2 such that (lo < √2 < hi),
-- and (hi - lo) < err
approximateSqrt2 :: Rational -> (Rational, Rational)
approximateSqrt2 err = go 1 (f 1)
  where
    -- √2 is a fixed point of f
    f a = 1 + 1 / (1 + a)
    go x y
     | abs (y - x) < err = if x < y then (x, y) else (y, x)
     | otherwise = go y (f y)

useDoubleThreshold :: Rational
useDoubleThreshold = 2 ^ (50 :: Int)

floorQSqrt2 :: QSqrt2 -> Integer
floorQSqrt2 (MkQSqrt2 a b)
  | b == 0 = na
  | b < useDoubleThreshold = na + mSmall
  | otherwise = na + mExact
  where
    na = floor a :: Integer
    a' = a - fromInteger na
    
    -- Residual
    r = MkQSqrt2 a' b

    -- Non-exact but correct for small value
    mSmall :: Integer
    mSmall
      | r < m     = mInteger - 1
      | r < m + 1 = mInteger
      | otherwise = mInteger + 1
      where
        -- Use mSmall only when | rDouble - residual | < 1
        rDouble = toDouble r
        mInteger = floor rDouble
        m = fromInteger mInteger

    -- Exact calculation
    mExact :: Integer
    mExact = if r < fromInteger (m + 1) then m else m + 1
      where
        (x, y) = approximateSqrt2 (1 / abs b)
        -- lo < residual = a' + b * √2 < hi < lo + 1
        lo = a' + (if b < 0 then b * y else b * x)
        m = floor lo
        -- m <= lo < residual < hi < lo * b + 1 <= ceil (lo * b + 1) <= m + 2
        -- m < residual < m + 2
        -- floor residual == m || floor residual == m + 1

properFractionQSqrt2 :: QSqrt2 -> (Integer, QSqrt2)
properFractionQSqrt2 x
  | x == 0 = (0, 0)
  | x < 0, frac == 0 = (-n, 0)
  | x < 0            = (-n, 1 - frac)
  | otherwise = (n, frac)
  where
    n = floorQSqrt2 (abs x)
    frac = abs x - fromInteger n
