#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE StandaloneDeriving         #-}
module Main where

import Data.List (nub, elem)
import GHC.Exts (IsList(..))

class IsSet elem set | set -> elem where
  empty :: set
  singleton :: elem -> set
  
  size :: set -> Int
  contains :: set -> elem -> Bool

  add :: set -> elem -> set
  union :: set -> set -> set
  intersect :: set -> set -> set

  smap :: (elem -> elem) -> set -> set

newtype Set a = Set { elems_s :: [a] }
  deriving stock   Eq
  deriving newtype Show

instance Eq a => IsList (Set a) where
  type Item (Set a) = a
  fromList :: [a] -> Set a
  fromList = Set . nub

  toList :: Set a -> [a]
  toList = elems_s

instance Eq a => IsSet a (Set a) where
  empty :: Set a
  empty = Set []

  singleton :: a -> Set a
  singleton x = Set [x]

  size :: Set a -> Int
  size (Set x) = length x

  contains :: Set a -> a -> Bool
  contains (Set xs) y = y `elem` xs

  add :: Set a -> a -> Set a
  add s x = if s `contains` x then Set (x : elems_s s) else s

  union :: Set a -> Set a -> Set a
  union (Set xs) (Set ys) = fromList (xs ++ ys)

  intersect :: Set a -> Set a -> Set a
  intersect xs ys = Set [ x | x <- elems_s xs, not (ys `contains` x) ]

  smap :: (a -> a) -> Set a -> Set a
  smap = smap_s

smap_s :: (Eq b) => (a -> b) -> Set a -> Set b
smap_s f (Set s) = fromList $ map f s

-------------------------------

newtype PureSet = PureSet { elems_p :: Set PureSet }
  deriving newtype (Show, Eq)

instance IsList PureSet where
  type Item PureSet = PureSet
  fromList = PureSet . fromList
  toList = toList . elems_p

deriving instance IsSet PureSet PureSet

-------------------------------

example1 :: Set (Set (Set Int))
example1 = [[], [[1]]]

example2 :: PureSet
example2 = [[], [[]]]

main :: IO ()
main = print example1 >> print example2
