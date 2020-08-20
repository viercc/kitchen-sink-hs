#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
{-# LANGUAGE DeriveFunctor #-}
module Main where

import Control.Applicative
import Control.Monad

data Tree a = Fail | Success a | Branch (Tree a) (Tree a)
  deriving (Show, Eq, Functor)

instance Applicative Tree where
  pure = Success
  (<*>) = ap

instance Alternative Tree where
  empty = Fail
  (<|>) = Branch

instance Monad Tree where
  return = pure
  
  Fail       >>= _ = Fail
  Success a  >>= k = k a
  Branch x y >>= k = Branch (x >>= k) (y >>= k)

instance MonadPlus Tree where
  mzero = empty
  mplus = (<|>)


test1 :: Tree Int
test1 = Branch Fail Fail

test2 :: Tree Int
test2 = Branch Fail (Branch (Success 1) (Success 2))

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
    coins = pure 3 <|> (pure 7 <|> pure 19)
    go xs n
      | n == 0    = Success xs
      | n < 0     = Fail
      | otherwise = coins >>= \x -> go (x:xs) (n-x)

test4 :: Tree [Int]
test4 = go [] 100
  where
    coins = pure 3 <|> (pure 7 <|> pure 19)
    go xs n
      | n == 0    = Success xs
      {- Oops, didn't check negatives. It will make infinite trees!
      | n < 0     = Fail
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
treeToLazy Fail         = Dead
treeToLazy (Success a)  = Final a
treeToLazy (Branch x y) = Next $ treeToLazy x <|> treeToLazy y

---------------------------------------------------------

dfs :: Tree a -> Maybe a
dfs Fail         = empty
dfs (Success a)  = pure a
dfs (Branch x y) = dfs x <|> dfs y

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
