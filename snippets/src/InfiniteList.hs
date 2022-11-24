{-# LANGUAGE DeriveFunctor #-}

module InfiniteList where

import Prelude hiding (foldr1)

data Infinite a = a :> Infinite a
  deriving (Functor)

foldr1 :: (a -> b -> b) -> Infinite a -> b
foldr1 step = let go (a :> as) = step a (go as) in go

foldlBreak :: (acc -> b -> Either r acc) -> acc -> Infinite b -> r
foldlBreak step = go
  where
    go acc (b :> bs) = case step acc b of
      Left r -> r
      Right acc' -> go acc' bs

foldlBreak_2 :: (acc -> b -> Either r acc) -> acc -> Infinite b -> r
foldlBreak_2 step acc0 bs = foldr1 step' bs acc0
  where
    step' b cont acc = case step acc b of
      Left r -> r
      Right acc' -> cont acc'

foldlBreak_3 :: (b -> a -> (b -> r) -> r) -> b -> Infinite a -> r
foldlBreak_3 step b0 as = foldr1 (\a k b -> step b a k) as b0