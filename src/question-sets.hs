{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}
module Set where

import Data.List (nub, elem)

newtype Set a = Set { elems_s :: [a] } deriving (Show, Eq)

class IsSet elem set | set -> elem where
  fromList :: [elem] -> set
  empty :: set
  singleton :: elem -> set

  size :: set -> Int
  contains :: set -> elem -> Bool

  add :: set -> elem -> set
  union :: set -> set -> set
  intersect :: set -> set -> set

  smap :: (elem -> elem) -> set -> set

instance Eq a => IsSet a (Set a) where
  fromList :: [a] -> Set a
  fromList = Set . nub

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

newtype PureSet = PureSet { elems_p :: Set PureSet } deriving (Show, Eq)

deriving instance IsSet PureSet PureSet

-------------------------------

example1 :: Set (Set (Set Int))
example1 = fromList [empty, fromList [empty]]

example2 :: PureSet
example2 = fromList [empty, fromList [empty]]

