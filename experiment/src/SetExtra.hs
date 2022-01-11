{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
module SetExtra (symdiff) where

import GHC.Exts(reallyUnsafePtrEquality#, isTrue#)
import Data.Set.Internal

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)

symdiff :: Ord a => Set a -> Set a -> Set a
symdiff !t1 !t2 | ptrEq t1 t2 = Tip
symdiff t1 Tip  = t1
symdiff Tip t2  = t2
symdiff (Bin _ x l1 r1) t2 = case splitMember x t2 of
  (l2, mx, r2) | mx        -> merge l1l2 r1r2
               | otherwise -> link x l1l2 r1r2
    where !l1l2 = symdiff l1 l2
          !r1r2 = symdiff r1 r2