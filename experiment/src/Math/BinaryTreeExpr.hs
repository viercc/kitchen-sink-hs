{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Math.BinaryTreeExpr where

import Data.List (sort, genericLength)
import Data.MemoCombinators qualified as Memo

import Math.Combinatorics (catalan)

data Tree = Leaf | Node Tree Tree deriving (Eq, Ord)

instance Show Tree where
  show = prettyInfix

-- 全二分木列挙（葉数 n）
trees :: Integer -> [Tree]
trees n
  | n <= 0 = []
  | n == 1 = [Leaf]
  | otherwise = [Node l r | i <- [1..n-1], l <- trees i, r <- trees (n-i)]

prettyInfix :: Tree -> String
prettyInfix = ($ "") . pretty'
  where
    pretty' Leaf = ('*' :)
    pretty' (Node l r) = ("(" ++) . pretty' l . (" , " ++) . pretty' r . (")" ++)

-- shortest expression
toShortestString :: Tree -> String
toShortestString = docToString . expr
  where
    dot = Lit '.'
    brace x = Lit '{' +++ x +++ Lit '}'

    expr Leaf = Lit '*'
    expr (Node l r) = expr l +++ factor r

    factor Leaf = Lit '*'
    factor (Node l r)
      | docLen dotCase < docLen braceCase = dotCase
      | otherwise = braceCase
      where
        dotCase = dot +++ factor l +++ factor r
        braceCase = brace (expr l +++ factor r)

-- cost-only
costF, costE :: Tree -> Integer
costF Leaf = 0
costF (Node l r) = min (1 + costF l + costF r) (2 + costE l + costF r)
costE Leaf = 0
costE (Node l r) = costE l + costF r

-- using spine:

spine :: Tree -> [Tree]
spine = \t -> go t []
  where
    go Leaf stack = stack
    go (Node l r) stack = go l (r : stack)

unspine :: [Tree] -> Tree
unspine ts = go Leaf ts
  where
    go t [] = t
    go t (u : us) = go (Node t u) us

newtype Tree' = Node' { children :: [Tree']}
  deriving (Eq, Ord)

instance Show Tree' where
  show = prettyTree'

prettyTree' :: Tree' -> String
prettyTree' (Node' []) = "*"
prettyTree' (Node' ts) = "*" ++ show ts


conv :: Tree -> Tree'
conv t = Node' (map conv (spine t))

unconv :: Tree' -> Tree
unconv t' = unspine (unconv <$> children t')

costE' :: Tree' -> Integer
costE' t = sum (costF' <$> children t)

costF' :: Tree' -> Integer
costF' t = penalty (children t) + costE' t
  where
    penalty [] = 0
    penalty [_] = 1
    penalty _ = 2

-- Tree' の全列挙
trees' :: Integer -> [Tree']
trees' n = [ Node' ts | ts <- forest' (n - 1) ]

forest' :: Integer -> [[Tree']]
forest' n
  | n < 0 = []
  | n == 0 = [[]]
  | otherwise =
      [ (t : ts) | k <- [1 .. n], t <- trees' k, ts <- forest' (n - k) ]


{-

[Remark]

length (trees' n) = length (trees n) = catalan (n - 1)
length (forest' n) = length (trees' (n + 1)) = catalan n

-}

{-

-- sum of costF over all trees of size (n + 1)
f, g :: Integer -> Integer
f n = sum (costF' <$> trees' (n + 1))
g n = sum (costE' <$> trees' (n + 1))

f n
 = sum (costF' <$> trees' (n+1))
 = sum [ costF' t | t <- trees' (n+1) ]
 = sum [ penalty (children t) + costE' t | t <- trees' (n+1) ]

f 0
 = sum [ costF' t | t <- trees' 1 ] = sum [ node [] ] = 0

f n
 = sum [ costF' t | t <- trees' (n + 1) ]
 = sum [ penalty (children t) + costE' t | t <- trees' (n + 1) ]
 = sum [ penalty (children t) | t <- trees' n ] + g n
 = sum [ penalty ts | ts <- forest' n ] + g n
 = sum [ penalty (t:ts) | k <- [1 .. n], t <- trees' k, ts <- forest' (n - k) ] + g n
 = sum [ penalty (t:ts) | k <- [1 .. n], t <- trees' k, ts <- forest' (n - k)]
   + g n
 = sum [ if ts == [] then 1 else 2 | k <- [1 .. n], _ <- trees' k, ts <- forest' (n - k) ]
   + g n
  -- (ts == []) <=> (k == n)
 = sum [ if k == n then 1 else 2 | k <- [1 .. n], _ <- trees' k, _ <- forest' (n - k) ]
   + g n
 = sum [ 2 - (if k == n then 1 else 0) | k <- [1 .. n], _ <- trees' k, _ <- forest' (n - k) ]
   + g n
 = sum [ 2 | k <- [1 .. n], _ <- trees' k, _ <- forest' (n - k) ]
   - sum [ 1 | let k = n, _ <- trees' n, _ <- forest' (n - k) ]
   + g n
 = sum [ 2 | _ <- trees' (n + 1) ]
   - sum [ 1 | _ <- trees' n ]
   + g n
 = 2 * catalan n - catalan (n - 1) + g n

g 0 = 0
g n
 = sum [ costE' t | t <- trees' (n+1)]
 = sum [ costE' (Node' ts) | ts <- forest' n]
 = sum [ sum (map costF' ts) | ts <- forest' n ]
 = sum [ sum $ map costF' (t : ts) | k <- [1 .. n], t <- trees' k, ts <- forest' (n - k) ]
 = sum [ costF' t + sum (map costF' ts) | k <- [1 .. n], t <- trees' k, ts <- forest' (n - k) ]
 = sum [ costF' t | k <- [1 .. n], t <- trees' k, _ <- forest' (n - k) ]
   + sum [ sum (map costF' ts) | k <- [1 .. n], _ <- trees' k, ts <- forest' (n - k) ]
 = sum [ f (k - 1) * catalan (n - k) | k <- [1 .. n] ]
   + sum [ catalan (k - 1) * g (n - k) | k <- [1 .. n] ]
 = sum [ f (k - 1) * catalan (n - k) | k <- [1 .. n] ]
   + sum [ g (k - 1) * catalan (n - k) | k <- [1 .. n] ]
 = sum [ (f (k - 1) + g (k - 1)) * catalan (n - k) | k <- [1 .. n] ]

-}

-- "sum of the costs" formula

-- sum of costF over all trees of size (n + 1)
sumCostF, sumCostE :: Integer -> Integer
sumCostF n
  | n <  0 = error ("sumCostF " ++ show n)
  | n == 0 = 0
  | otherwise = 2 * catalan n - catalan (n - 1) + sumCostE n
sumCostE = g
  where
    g' n 
      | n <  0 = error ("sumCostE " ++ show n)
      | n == 0 = 0
      | otherwise = sum [ (f (k - 1) + g (k - 1)) * catalan (n - k) | k <- [1 .. n] ]
    g = Memo.integral g'
    f = sumCostF

avgCostF, avgCostE :: Integer -> Double
avgCostF n = fromIntegral (sumCostF n) / fromIntegral (n + 1) / fromIntegral (catalan n)
avgCostE n = fromIntegral (sumCostE n) / fromIntegral (n + 1) / fromIntegral (catalan n)

-- Explicit formula (?)
explicitSumCostF :: Integer -> Integer
explicitSumCostF n
  | n < 0  = error ("explicitSumCostF " ++ show n)
  | n == 0 = 0
  | otherwise = (3 * n - 2) * catalan (n - 1)

explicitSumCostE :: Integer -> Integer
explicitSumCostE n
  | n < 0  = error ("explicitSumCostE " ++ show n)
  | n == 0 = 0
  | otherwise = (3 * (n - 1) * (n - 1) * catalan (n - 1)) `div` (n + 1)


{-

From

  f n = 2 * catalan n - catalan (n - 1) + g n

and

  f n = (3 * n - 2) * catalan (n - 1),

an explicit formula for g is

  g n
    = f n - 2 * catalan n + catalan (n - 1)
    = (3 * n - 2) * catalan (n - 1) - 2 * catalan n + catalan (n - 1)
    = (3 * n - 1) * catalan (n - 1) - 2 * 2 * (2 * n - 1) / (n + 1) * catalan (n - 1)
    = ((3 * n - 1) * (n + 1) - 4 * (2 * n - 1)) / (n + 1) * catalan (n - 1)
    = (3n^2 + 2n - 1 - 8n + 4) / (n + 1) * catalan (n - 1)
    = (3n^2 - 6n + 3) / (n + 1) * catalan (n - 1)
    = 3*(n^2 - 2n + 1) / (n + 1) * catalan (n - 1)
    = 3 * (n - 1)^2 / (n + 1) * catalan (n - 1)

-}

-- * Sanity checks

-- Returns list of counterexamples
equiv :: (Eq a) => (k -> a) -> (k -> a) -> [k] -> [(k, a, a)]
equiv f g ks = [ (k, fk, gk) | k <- ks, let fk = f k, let gk = g k, fk /= gk ]

checkTreeNum_Catalan :: [(Integer, Integer, Integer)]
checkTreeNum_Catalan = equiv (genericLength . trees) (catalan . pred) [1 .. 10]

checkEnumeration :: [(Integer, [Tree], [Tree])]
checkEnumeration = equiv (sort . trees) (sort . map unconv . trees') [1 .. 10]

checkCost_Cost' :: [(Tree, Integer, Integer)]
checkCost_Cost' = equiv costE (costE' . conv) ([1 .. 10] >>= trees)

checkSumCost :: [(Integer, Integer, Integer)]
checkSumCost = equiv (\n -> sum (costE' <$> trees' (n + 1))) sumCostE [1 .. 10]

checkExplicitF :: [(Integer, Integer, Integer)]
checkExplicitF = equiv sumCostF explicitSumCostF [1..20]

checkExplicitE :: [(Integer, Integer, Integer)]
checkExplicitE = equiv sumCostE explicitSumCostE [1..20]

-- * Utility

data Doc = Lit !Char | Concat !Integer !Doc !Doc

docLen :: Doc -> Integer
docLen (Lit _) = 1
docLen (Concat n _ _) = n

(+++) :: Doc -> Doc -> Doc
x +++ y = Concat (docLen x + docLen y) x y

docToString :: Doc -> String
docToString = \xs -> go xs ""
  where
    go (Lit c) = (c :)
    go (Concat _ x y) = go x . go y
