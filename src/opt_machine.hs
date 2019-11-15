module Main where

import qualified Data.MemoCombinators as Memo

{-

[Question]

We have a stack machine with just 2 instructions:

    Dup = x <- pop; push x; push x
    Add = x <- pop; y <- pop; push (x + y);

For fixed N, find the optimal (the shortest) program that performs

    x <- pop; push (N * x)

e.g.

    Both

      p1 = [Dup, Dup, Dup, Add, Add, Add]
      p2 = [Dup, Add, Dup, Add]

    Performs (N *), but p2 is shorter. In fact, p2 is the
    shortest one among such programs.

-}

data Instruction = Dup | Add
    deriving (Show, Read, Eq, Ord)

run :: [Instruction] -> [Int] -> [Int]
run [] xs = xs
run (Dup:ps) (x:xs) = run ps (x:x:xs)
run (Add:ps) (x:y:xs) = run ps (x+y : xs)
run _ _ = error "Ran out stack values"

{-

[Answer]

First, by replacing Dup with opening parenthesis '(' and Add with
closing parenthesis ')', the "valid" program (which does not run out stack
and leave exactly same number of values at stack) corresponds to
string of matching parens.

From this observation, it can be said that "valid" programs can be made
only by the following constructions:

* `[]`
* `[Dup] ++ p ++ [Add]` where `p` is valid
* `p ++ q` where `p` and `q` are valid

Let `eval :: [Instruction] -> Int -> Int` be a function, which takes
a *valid* program and a initial stack top value, and returns the
final stack top value. Then,

* `eval [] = id = (1 *)`
* `eval ([Dup] ++ p ++ [Add]) = \x -> x + eval p x`
* `eval (p ++ q) = eval p . eval q`

And it can be said that

* `eval p = (coef p *)`
* `coef [] = 1`
* `coef ([Dup] ++ p ++ [Add]) = 1 + coef p`
* `coef (p ++ q) = coef p * coef q`

-}

eval :: [Instruction] -> Int -> Int
eval p x = case run p [x] of
  [y] -> y
  _   -> error "invalid program"

data Expr = Id | Succ Expr | Mul Expr Expr
    deriving (Show, Read, Eq, Ord)

toProgram :: Expr -> [Instruction]
toProgram = ($ []) . go
  where
    go Id = id
    go (Succ e) = (Dup :) . go e . (Add :)
    go (Mul e e') = go e . go e'

-- eval (toProgram e) x = coef e * x
coef :: Expr -> Int
coef Id = 1
coef (Succ e) = 1 + coef e
coef (Mul e e') = coef e * coef e'

-- length (toProgram e) = 2 * cost e
cost :: Expr -> Int
cost Id = 0
cost (Succ e) = 1 + cost e
cost (Mul e e') = cost e + cost e'


binaryExpr :: Int -> Expr
binaryExpr n
  | n <= 0    = undefined
  | n == 1    = Id
  | n == 2    = Succ Id
  | n == 3    = Succ (Succ Id)
  | even n    = Mul twice (binaryExpr (n `div` 2))
  | otherwise = Succ (Mul twice (binaryExpr (n `div` 2)))
  where
    twice = Succ Id

optimalExpr :: Int -> (Int, Expr)
optimalExpr = Memo.integral go
  where
    go n
      | n <  1    = error "Wrong!!!"
      | n == 1    = (0, Id)
      | otherwise = minimum $
          [ let (w,e) = optimalExpr (n-1) in (w+1, Succ e) ] ++
          [ (w+w', Mul e e')
            | (j,k) <- factors n
            , let (w,  e) = optimalExpr j
            , let (w', e') = optimalExpr k
          ]

factors :: Int -> [(Int, Int)]
factors n =
  [ (j,k) | j <- takeWhile (\x -> x * x <= n) [2..]
          , let (k, r) = quotRem n j
          , r == 0 ]

primeFactorize :: Int -> [Int]
primeFactorize n
  | n <= 0    = undefined
  | otherwise = go 2 n
  where
    go p k
      | p * p > k  = [k]
      | otherwise  =
          case quotRem k p of
            (k', 0) -> p : go p k'
            _       -> go (p+1) k

main :: IO ()
main = mapM_ (print . optimalExpr) [2..255]
