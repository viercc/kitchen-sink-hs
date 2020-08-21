#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
{-# LANGUAGE DeriveFunctor #-}
module Main where

import Control.Applicative
import Control.Monad

data Tree a = Leaf a | Branch [Tree a]
  deriving (Show, Eq, Functor)

instance Applicative Tree where
  pure = Leaf
  (<*>) = ap

instance Alternative Tree where
  empty = Branch []
  x <|> y = Branch [x,y]

instance Monad Tree where
  return = pure
  
  Leaf a    >>= k = k a
  Branch xs >>= k = Branch (map (>>= k) xs)

instance MonadPlus Tree where
  mzero = empty
  mplus = (<|>)

test1 :: Tree Int
test1 = empty <|> empty

test2 :: Tree Int
test2 = empty <|> (pure 1 <|> pure 2)

{- Solves puzzle:
 A gold coin worth 3 silver coins,
a platinum coin worth 7 silver coins,
and a diamond gem worth 19 silver coins.

How can you pay for 100 silver coin worthy item
using no silver coins?
-}
test3 :: Tree [Int]
test3 = go [] 100
  where
    coins = Branch $ return <$> [3,7,19]
    go xs n
      | n == 0    = return xs
      | n < 0     = mzero
      | otherwise = coins >>= \x -> go (x:xs) (n-x)

test4 :: Tree [Int]
test4 = go [] 100
  where
    coins = Branch $ return <$> [3,7,19]
    go xs n
      | n == 0    = return xs
      {- Oops, didn't check negatives. It will make infinite trees!
      | n < 0     = mzero
      -}
      | otherwise = coins >>= \x -> go (x:xs) (n-x)

---------------------------------------------------------

data Lazy a = Dead | Final a | Next (Lazy a)
  deriving (Show, Eq, Functor)

instance Applicative Lazy where
  pure  = Final
  (<*>) = ap

instance Alternative Lazy where
  empty = Dead
  Dead    <|> y       = y
  x       <|> Dead    = x
  Final a <|> _       = Final a
  _       <|> Final a = Final a
  Next x' <|> Next y' = Next (x' <|> y')

instance Monad Lazy where
  return = pure
  Dead    >>= _ = Dead
  Final a >>= k = k a
  Next x  >>= k = Next (x >>= k)

instance MonadPlus Lazy where
  mzero = empty
  mplus = (<|>)

fromLazy :: Lazy a -> Maybe a
fromLazy Dead      = Nothing
fromLazy (Final a) = Just a
fromLazy (Next x)  = fromLazy x

treeToLazy :: Tree a -> Lazy a
treeToLazy (Leaf a)    = Final a
treeToLazy (Branch xs) =
  Next $ tfold Dead (<|>) $ (treeToLazy <$> xs)

tfold :: a -> (a -> a -> a) -> [a] -> a
tfold zero op = go
  where
    go []  = zero
    go [a] = a
    go as  = go (pairs as)

    pairs (a : b : rest) = op a b : pairs rest
    pairs as = as

---------------------------------------------------------

dfs :: Tree a -> Maybe a
dfs (Leaf a)    = pure a
dfs (Branch xs) = foldr (<|>) Nothing $ dfs <$> xs

bfs :: Tree a -> Maybe a
bfs = fromLazy . treeToLazy

main :: IO ()
main = do
  putStrLn "=== dfs ==="
  print $ dfs test1
  print $ dfs test2
  print $ dfs test3
  -- This try to search infinitely deep
  -- branch, leading infinite loop (while consuming
  -- unlimited amount of memory!)
  -- 
  -- print $ dfs test4
  
  putStrLn "=== bfs ==="
  print $ bfs test1
  print $ bfs test2
  print $ bfs test3
  print $ bfs test4
