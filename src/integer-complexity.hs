{-# LANGUAGE BangPatterns #-}
module Main(main) where

import Math.NumberTheory.Logarithms
import qualified Data.MemoCombinators as Memo

import qualified Data.Vector as V

cost2 :: Integer -> Int
cost2 = loop 0
  where loop !acc 0 = acc - 2
        loop !acc n = case quotRem n 2 of
          (q, r) -> loop (acc + 2 + fromInteger r) q

data Expr = Leaf !Int | Plus !Expr !Expr | Times !Expr !Expr
  deriving (Eq, Ord)

instance Num Expr where
  fromInteger = Leaf . fromInteger
  (+) = Plus
  (*) = Times

instance Show Expr where
  showsPrec p (Leaf n) = showsPrec p n
  showsPrec p (Plus x y) = showParen (6 < p) $ showsPrec 7 x . (" + " ++) . showsPrec 6 y
  showsPrec p (Times x y) = showParen (7 < p) $ showsPrec 8 x . (" * " ++) . showsPrec 7 y

solve :: Integer -> Int -> Maybe (Expr, Int)
solve = solveAux
  where
    solveAux n | n < tableSize' = restrict (table V.! fromInteger n)
               | otherwise      = solveRaw n
    
    restrict ma maxSize = ma >>= \(_, ca) -> if ca < maxSize then ma else Nothing

    tableSize :: Int
    tableSize = 10000000

    tableSize' :: Integer
    tableSize' = toInteger tableSize

    table :: V.Vector (Maybe (Expr, Int))
    table = V.generate tableSize $ \i ->
      let i' = fromIntegral i
      in solveRaw i' (1 + cost2 i')

solveRaw :: Integer -> Int -> Maybe (Expr, Int)
solveRaw n maxSize =
  solveLeaf n maxSize `merge` solvePlus n maxSize `merge` solveTimes n maxSize

merge :: (Ord cost) => Maybe (a, cost) -> Maybe (a, cost) -> Maybe (a, cost)
merge ma mb = case ma of
  Nothing      -> mb
  Just (_, ca) -> case mb of
    Nothing -> ma
    Just (_,cb) | ca <= cb  -> ma
                | otherwise -> mb

solveLeaf :: Integer -> Int -> Maybe (Expr, Int)
solveLeaf n cmax
  | n <= cmax' = Just (Leaf n', n')
  | otherwise  = Nothing
  where n' = fromInteger n :: Int
        cmax' = min 5 (toInteger cmax - 1)

solvePlus :: Integer -> Int -> Maybe (Expr, Int)
solvePlus n cmax = foldr merge Nothing $
  do (j,k) <- splitPlus n cmax
     Just (jExpr, cj) <- [solve j cmax]
     Just (kExpr, ck) <- [solveLeaf k (cmax - cj), solveTimes k (cmax - cj)]
     return $ Just (Plus jExpr kExpr, cj + ck)

splitPlus :: Integer -> Int -> [(Integer, Integer)]
splitPlus n cmax
  | n <= 5 = []
  | otherwise =
      takeWhile cond [(j, n-j) | j <- [1 .. n `div` 2] ]
  where
    cond (j,k) = lowerBound j k <= cmax

    lowerBound j k | j <= 5    = fromInteger j + 3 * integerLogBase 3 k
                   | otherwise = 3 * integerLogBase 3 (j * k)

solveTimes :: Integer -> Int -> Maybe (Expr, Int)
solveTimes n cmax = foldr merge Nothing $
  do (j,k) <- splitTimes n
     Just (jExpr, cj) <- [solve j cmax]
     Just (kExpr, ck) <- [solve k (cmax - cj)]
     return $ Just (Times jExpr kExpr, cj + ck)

splitTimes :: Integer -> [(Integer, Integer)]
splitTimes = Memo.integral splitTimes'
  where
    splitTimes' n | n <= 5 = []
    splitTimes' n =
      [ (j, k) | j <- takeWhile (\i -> i*i <= n) [2..]
               , let (k, r) = quotRem n j
               , r == 0 ]

main :: IO ()
main = print $ solve (2 ^ n) (2 * n + 1)
  where n = 34 :: Int
