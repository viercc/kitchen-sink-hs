{-# LANGUAGE BangPatterns #-}
module Data.IntEquivalence(
  Equiv,
  emptyEquiv, equate,
  find, findAll, classes
) where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | Data structure containing Equivalence relation on @Int@
newtype Equiv = Equiv Equiv_

-- | Underlying data
type Equiv_ = IntMap EquivNode

data EquivNode =
    Repr !Int -- ^ max depth of the class
  | Internal !Int -- ^ parent node

emptyEquiv :: Equiv
emptyEquiv = Equiv IntMap.empty

pathcompFind :: Int -> Equiv_ -> (Int, Int, Equiv_)
pathcompFind x eqv = case IntMap.lookup x eqv of
  Nothing -> (x, 0, eqv)
  Just (Repr d) -> (x, d, eqv)
  Just (Internal x') ->
    let (root, d, eqv') = pathcompFind x' eqv
        !eqv'' = IntMap.insert x (Internal root) eqv'
    in (root, d, eqv'')

find :: Int -> Equiv -> Int
find x (Equiv eqv) = case IntMap.lookup x eqv of
  Nothing -> x
  Just (Repr _) -> x
  Just (Internal x') -> find x' (Equiv eqv)

equate :: Int -> Int -> Equiv -> Equiv
equate x y (Equiv eqv) = Equiv eqv'''
  where
    (x', dx, eqv') = pathcompFind x eqv
    (y', dy, eqv'') = pathcompFind y eqv'
    eqv''' = case compare dx dy of
      LT -> IntMap.insert x' (Internal y') eqv''
      EQ -> IntMap.insert x' (Repr (dx + 1)) $
            IntMap.insert y' (Internal x') eqv''
      GT -> IntMap.insert y' (Internal x') eqv''

findAll :: Equiv -> IntMap Int
findAll (Equiv eqv0) = go repMap1 eqv1
  where
    getRepr x (Repr _) = Just x
    getRepr _ (Internal _) = Nothing

    getInternal (Repr _) = Nothing
    getInternal (Internal x') = Just x'

    repMap1 = IntMap.mapMaybeWithKey getRepr eqv0
    eqv1 = IntMap.mapMaybe getInternal eqv0

    go repMap eqv = case IntMap.minViewWithKey eqv of
      Nothing -> repMap
      Just ((x, x'), eqv') -> loop x' [x] repMap eqv'
    
    loop x path repMap eqv = case IntMap.lookup x repMap of
      Just x' -> found x' (x:path) repMap eqv
      Nothing -> case IntMap.lookup x eqv of
        Just x' -> loop x' (x:path) repMap eqv
        -- This case should not happen for a valid input
        Nothing -> error $ "dangling entry in Equiv? " ++ show (x : path, eqv)
    
    found x path repMap eqv =
      let repMap' = IntMap.union (IntMap.fromList [(y,x) | y <- path]) repMap
          eqv' = foldl' (flip IntMap.delete) eqv path
      in go repMap' eqv'

classes :: Equiv -> [IntSet]
classes eqv = IntMap.elems invMap
  where
    invMap = IntMap.fromListWith IntSet.union
      [ (rep, IntSet.singleton x) | (x,rep) <- IntMap.toList (findAll eqv) ]