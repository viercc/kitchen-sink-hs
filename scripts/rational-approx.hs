#!/usr/bin/env cabal
{- cabal:
build-depends: base, integer-logarithms, arithmoi
-}
import Data.Ratio
import Math.NumberTheory.Logarithms
import Math.NumberTheory.Powers.Squares

approx :: (Rational -> Ordering) -> [Rational]
approx f = go (0,1) (1, 1)
  where
    go :: (Integer, Integer) -> (Integer, Integer) -> [Rational]
    go (aLo, bLo) (aHi, bHi) =
      let aMid = aLo + aHi
          bMid = bLo + bHi
          mid = aMid % bMid
      in case f mid of
           LT -> mid : go (aLo, bLo) (aMid, bMid)
           EQ -> [mid]
           GT -> mid : go (aMid, bMid) (aHi, bHi)

approxSqrt :: Integer -> [Rational]
approxSqrt x | x < 0 = error "Negative sqrt"
             | otherwise =
    let (n,r) = integerSquareRootRem x
        sqrt' frac =
          let a = numerator frac
              b = denominator frac
          in compare (r * b * b) (a * (2*n*b + a))
    in if r == 0 then [n % 1] else (fromInteger n +) <$> approx sqrt'

approxLogBase :: Integer -> Integer -> [Rational]
approxLogBase _ 1 = [0]
approxLogBase x y = case compare x y of
  EQ -> [1]
  LT -> let n = toInteger $ integerLogBase x y
        in (fromInteger n +) <$> approx (logBase' x y n)
  GT -> recip <$> approxLogBase y x

logBase' :: Integer -> Integer -> Integer -> Rational -> Ordering
logBase' x y n frac =
  let a = numerator frac
      b = denominator frac
  in compare (y^b) (x^(a + n*b))

precision :: Integer -> [Rational] -> Rational
precision prec = head . dropWhile (\x -> denominator x < prec)

atDoublePrecision :: [Rational] -> Double
atDoublePrecision [] = error "empty approximation sequence"
atDoublePrecision (x:xs) = go (fromRational x) xs
  where
    go :: Double -> [Rational] -> Double
    go x' [] = x'
    go x' (y:ys) =
      let y' = fromRational y
      in if x' == y' then x' else go y' ys

p :: String -> IO ()
p = putStrLn

main :: IO ()
main = do
  let as = approxSqrt 15
  p "sqrt 15"
  p $ "  as[0..9] = " ++ show (take 10 as)
  p $ "  at 4-digits prec = " ++ show (fromRational $ precision 10000 as)
  p $ "  at double prec = " ++ show (atDoublePrecision as)

  let bs = approxLogBase 2 11
  p "logBase 2 11"
  p $ "  bs[0..9] = " ++ show (take 10 bs)
  p $ "  at 4-digits prec = " ++ show (fromRational $ precision 10000 bs)
  p $ "  at double prec = " ++ show (atDoublePrecision bs)
