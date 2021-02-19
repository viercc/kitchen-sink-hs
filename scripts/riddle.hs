#!/usr/bin/env cabal
{- cabal:
build-depends: base, containers
-}
{-# LANGUAGE DeriveTraversable #-}
{- |
https://www.reddit.com/r/haskell/comments/llsmtd/struggle_brute_forcing_solution_to_math_problem/
-}
module Main where

import Data.Semigroup
import Control.Applicative
import Data.Foldable (toList)
import Data.List (sort, intercalate)
import Control.Monad (guard)
import Data.Bifunctor (second)

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

newtype Bag a = Bag { unBag :: Map a Int }
  deriving (Show, Eq, Ord)

bag :: Ord a => [a] -> Bag a
bag = Bag . Map.fromListWith (+) . map (\a -> (a,1))

count :: Bag a -> Int
count = sum . unBag

pick :: (Ord a) => Bag a -> [(a, Bag a)]
pick (Bag xs) = fmap pickAt (Map.toAscList xs)
  where
    pickAt (a,n)
      | n > 1     = (a, Bag (Map.adjust pred a xs))
      | otherwise = (a, Bag (Map.delete a xs))

edgeValues :: Bag Int
edgeValues = bag [1,1,2,3,4,5,5,6,7,8,9,10]
-- edgeValues = bag [1 .. 12]

start, goal :: Int
start = 1
goal = 20
-- goal = 23

takePermutationsN :: (Ord a) => Int -> Bag a -> [([a], Bag a)]
takePermutationsN n xs
  | count xs < n = []
  | otherwise    = go n xs
  where
    go 0 ys = [([], ys)]
    go k ys =
      do (y, ys') <- pick ys
         (zs, rest) <- go (k-1) ys'
         pure (y:zs, rest)

{-

a --- b --- c
|     |     |
d --- e --- f
|     |     |
g --- h --- i

-}

data V3 a = V3 a a a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative V3 where
  pure a = V3 a a a
  V3 x y z <*> V3 x' y' z' = V3 (x x') (y y') (z z')

newtype Square a = Square (V3 (V3 a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

solveUniq :: Bag Int -> [Square Int]
solveUniq xs = do
  ([ab, be, ad, de], xs') <- takePermutationsN 4 xs
  guard $ ab + be == ad + de
  
  -- symSlash
  guard $ ab <= ad
  -- symBackslash
  guard $ 2 * (ab + be) <= goal - start
  
  ([bc, cf, ef], xs'') <- takePermutationsN 3 xs'
  guard $ bc + cf == be + ef
  -- symElbow1
  guard $ bc <= cf
  
  ([eh, dg, gh], xs''') <- takePermutationsN 3 xs''
  guard $ de + eh == dg + gh
  -- symElbow2
  guard $ dg <= gh
  
  ([fi, hi], _) <- takePermutationsN 2 xs'''
  guard $ ef + fi == eh + hi
  let {
    a = start;  b = a + ab; c = b + bc;
    d = a + ad; e = d + de; f = e + ef;
    g = d + dg; h = g + gh; i = h + hi;
    ans = V3 (V3 a b c) (V3 d e f) (V3 g h i)
  }
  guard (i == goal)
  pure (Square ans)

solve :: Bag Int -> [Square Int]
solve xs = do
  ([ab, be, ad, de], xs') <- takePermutationsN 4 xs
  guard $ ab + be == ad + de
  ([bc, cf, ef], xs'') <- takePermutationsN 3 xs'
  guard $ bc + cf == be + ef
  ([eh, dg, gh], xs''') <- takePermutationsN 3 xs''
  guard $ de + eh == dg + gh
  ([fi, hi], _) <- takePermutationsN 2 xs'''
  guard $ ef + fi == eh + hi
  let {
    a = start;  b = a + ab; c = b + bc;
    d = a + ad; e = d + de; f = e + ef;
    g = d + dg; h = g + gh; i = h + hi;
    ans = V3 (V3 a b c) (V3 d e f) (V3 g h i)
  }
  guard (i == goal)
  pure (Square ans)

verify :: Square Int -> Bool
verify (Square (V3 (V3 a b c) (V3 d e f) (V3 g h i))) =
  a == start && i == goal && bag edges == edgeValues
  where
    edges = [ b - a, c - b
            , d - a, e - b, f - c
            , e - d, f - e
            , g - d, h - e, i - f
            , h - g, i - h
            ]

transpose :: Square a -> Square a
transpose (Square ass) = Square (sequenceA ass)

reflect :: Square a -> Square a
reflect (Square ass) = Square $ reflectV3 . fmap reflectV3 $ ass
  where
    reflectV3 :: V3 x -> V3 x
    reflectV3 (V3 x y z) = V3 z y x

symSlash :: Square Int -> Square Int
symSlash = transpose

symBackslash :: Square Int -> Square Int
symBackslash = fmap (\x -> start + goal - x) . reflect

{- Elbow!

     +bc
-> b --> c
   |     | + cf
         v
      -> f
---------------------
     +cf
-> b --> c'
   |     | +bc
         v
      -> f

b + bc + cf = f
b + f = b + b + bc + cf
      = (b + bc) + (b + cf)
      = c + c'
-}

symElbow1, symElbow2 :: Square Int -> Square Int
symElbow1 (Square (V3 (V3 a b c) def@(V3 _ _ f) ghi))
  = Square (V3 (V3 a b (b + f - c)) def ghi)
symElbow2 (Square (V3 abc def@(V3 d _ _) (V3 g h i)))
  = Square (V3 abc def (V3 (d + h - g) h i))

uniqToAll :: Square Int -> [Square Int]
uniqToAll sq = [sq]
  >>= optionally symElbow1
  >>= optionally symElbow2
  >>= optionally symSlash
  >>= optionally symBackslash
  where
    optionally :: Eq a => (a -> a) -> a -> [a]
    optionally f a =
      let a' = f a in [a] ++ [a' | a /= a']

main :: IO ()
main = do
  let solutionsAll = sort $ solve edgeValues
      solutionsUniq = sort $ solveUniq edgeValues
      solutionsRecover = sort $ solutionsUniq >>= uniqToAll
  putStrLn $ "#all = " ++ show (length solutionsAll)
  mapM_ pretty solutionsAll
  putStrLn $ "#uniq = " ++ show (length solutionsUniq)
  mapM_ pretty solutionsUniq
  putStrLn $ "#recover = " ++ show (length solutionsRecover)
  mapM_ pretty solutionsRecover

  putStrLn $ "all == recover?"
  print $ solutionsAll == solutionsRecover
  
  where
    dd n = filler ++ str
      where
        str = show n
        len = length str
        filler = replicate (2 - length str) ' '
    sepBy separator = intercalate separator . toList
    fmt (Square v) = sepBy "|" . fmap (sepBy " ") $ fmap (fmap dd) v
    
    pretty sq = putStrLn $ fmt sq ++ (if verify sq then "" else "## BAD! ##")
