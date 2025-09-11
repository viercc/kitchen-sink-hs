{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
module Impredic where

x :: Show a => a -> String
x = show

f :: ((Show a) => a -> b) -> a -> b
f = undefined

(&) :: a -> (a -> b) -> b
(&) = flip id

def1, def2, def3 :: a -> String
def1 = f x
def2 = f $ x
def3 = x & f
