{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
module MapClass where

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap
import           Data.Monoid
import           Data.List (foldl')

{- |

Laws for IsMap:

  1. lookup k mempty = mempty
  2. lookup k (x `mappend` y) = lookup k x `mappend` lookup k y
  3. lookup j (singleton k v) = if j == k then v else mempty

-}
class (Functor m, Eq (Key m)) => IsMap m where
  type Key m :: *

  empty :: m a
  union :: m a -> m a -> m a
  intersectionWith :: (a -> b -> c) -> m a -> m b -> m c
  
  intersection :: m a -> m b -> m a
  intersection = intersectionWith const
  
  singleton :: Key m -> a -> m a
  lookup :: Key m -> m a -> Maybe a
  delete :: Key m -> m a -> m a
  
  insert :: Key m -> a -> m a -> m a
  insert k v m = singleton k v `union` m
  
  fromList :: [(Key m, a)] -> m a
  fromList = foldl' (\m (k,v) -> insert k v m) empty
