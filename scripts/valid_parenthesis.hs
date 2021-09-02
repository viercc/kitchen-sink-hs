-- https://www.reddit.com/r/haskell/comments/opedyx/simplest_solution_to_valid_parentheses_problem/
module Main where

import Data.Foldable (toList)
import Data.Semigroup
import System.Environment (getArgs)

data Symbol = Paren | Brace | Bracket
  deriving (Show, Eq)

data Balance = Balance [Symbol] [Symbol] | Irreducible
  deriving (Show, Eq)

openSym, closeSym :: Symbol -> Balance
openSym s = Balance [] [s]
closeSym s = Balance [s] []

instance Semigroup Balance where
  Irreducible <> _ = Irreducible
  _ <> Irreducible = Irreducible
  Balance cl1 op1 <> Balance cl2 op2 = case go op1 cl2 of
    Balance cl' op' -> Balance (cl1 ++ cl') (op' ++ op2)
    Irreducible    -> Irreducible
    where
      go [] cs = Balance cs []
      go os [] = Balance [] os
      go (c:cs) (o:os) | c == o    = go cs os
                       | otherwise = Irreducible
  
  sconcat = treefold . toList

instance Monoid Balance where
  mempty = Balance [] []
  mconcat = treefold

treefold :: (Monoid x) => [x] -> x
treefold [] = mempty
treefold [x] = x
treefold (x:y:xs)  = treefold (x <> y : pairs xs)
  where
    pairs (a:b:as) = a <> b : pairs as
    pairs as = as

toSymbol :: Char -> Maybe Balance
toSymbol '(' = Just $ openSym Paren
toSymbol ')' = Just $ closeSym Paren
toSymbol '{' = Just $ openSym Brace
toSymbol '}' = Just $ closeSym Brace
toSymbol '[' = Just $ openSym Bracket
toSymbol ']' = Just $ closeSym Bracket
toSymbol _   = Nothing

judge :: String -> Maybe Balance
judge str = mconcat <$> traverse toSymbol str

main :: IO ()
main = getArgs >>= mapM_ printJudge
  where
    printJudge s = putStrLn $ s ++ " => " ++ show (judge s)
