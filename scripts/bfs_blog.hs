#!/usr/bin/env cabal
{- cabal:
build-depends: base, containers
ghc-options: -Wall
-}

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Monoid (First(..))
import qualified Data.Sequence as S
import Data.Sequence (Seq(Empty, (:<|), (:|>)))

type Coin  = Int
type Value = Int

type Graph label node = node -> [(label, node)]

type Tree node = node -> [node]

addCoin :: Graph Coin Value
addCoin !n = [ (c,n+c) | c <- [3,7,19], n+c <= 100 ]

addCoin' :: Tree ([Coin], Value)
addCoin' = graphToPaths addCoin

firstJust :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
firstJust f = getFirst . foldMap (First . f)

graphToPaths :: Graph label node -> Tree ([label], node)
graphToPaths graph (path, node)
  = [ (l : path, node') | (l, node') <- graph node ]

bfSeq :: Tree node -> node -> [node]
bfSeq step root = loop (S.singleton root)
  where
    loop Empty     = []
    loop (n :<| q) = n : loop (foldl' (:|>) q (step n))

solvePuzzleSeq :: Maybe [Coin]
solvePuzzleSeq = firstJust f $ bfSeq addCoin' ([], 0)
  where f (path, 100) = Just (reverse path)
        f _           = Nothing

-------------------------------------------------------

bfList :: Tree node -> node -> [node]
bfList step root =
    let ans = root : go 1 ans
     in ans
  where
    go n _ | n <= 0 = []
    go n (x:xs) = 
      let children = step x
      in children ++ go (n - 1 + length children) xs
    go _ [] = error "Never reach here"

solvePuzzleList :: Maybe [Coin]
solvePuzzleList = firstJust f $ bfList addCoin' ([], 0)
  where f (path, 100) = Just (reverse path)
        f _           = Nothing

-----------------------------------------

data Lazy a = Fail | Ok a | Next (Lazy a)
  deriving (Functor, Foldable, Traversable)

forceLazy :: Lazy a -> Maybe a
forceLazy Fail     = Nothing
forceLazy (Ok a)   = Just a
forceLazy (Next x) = forceLazy x

instance Applicative Lazy where
  pure = Ok
  (<*>) = ap

instance Alternative Lazy where
  empty = Fail
  Fail   <|> y      = y
  Ok a   <|> _      = Ok a
  x      <|> Fail   = x
  _      <|> Ok a   = Ok a
  Next x <|> Next y = Next (x <|> y)

instance Monad Lazy where
  return = pure
  Fail   >>= _ = Fail
  Ok a   >>= k = k a
  Next x >>= k = Next (x >>= k)

bfSearchLazy :: Tree node -> node -> (node -> Lazy a) -> Lazy a
bfSearchLazy step root goal = go root
  where
    go x = goal x <|> Next (asum $ fmap go (step x))

solvePuzzleLazy :: Maybe [Coin]
solvePuzzleLazy = forceLazy $ bfSearchLazy addCoin' ([], 0) f
  where f (path, 100) = Ok (reverse path)
        f _           = Fail

-----------------------------------------

main :: IO ()
main = do
  putStrLn "# Seq"
  print solvePuzzleSeq
  putStrLn "# List"
  print solvePuzzleList
  putStrLn "# Lazy"
  print solvePuzzleLazy
