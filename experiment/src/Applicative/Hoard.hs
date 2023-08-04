{-# LANGUAGE DeriveFunctor #-}
module Applicative.Hoard where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A strange Applicative!
-- 
-- @Hoard k v a@ basically behave like the applicative of
-- functions @Map k v -> a@,
-- but you can specify a set of keys to hoard by a computation.
-- 
-- When combining multiple computations, if a key is hoarded by
-- one or more computations, that key is removed from maps passed to
-- non-hoarding computations.
data Hoard k v a = Hoard (Set k) (Map k v -> a)
  deriving (Functor)

instance (Ord k) => Applicative (Hoard k v) where
  pure a = Hoard Set.empty (const a)
  Hoard ks f <*> Hoard ks' f' = Hoard (Set.union ks ks') g
    where
      g dict = f (dict `Map.withoutKeys` (ks' Set.\\ ks)) $ f' (dict `Map.withoutKeys` (ks Set.\\ ks'))

runHoard :: Hoard k v a -> Map k v -> a
runHoard (Hoard _ f) = f

-- | Just looks up a key
query :: Ord k => k -> Hoard k v (Maybe v)
query k = Hoard Set.empty (Map.lookup k)

-- | Looks up a key and hoard it
hoard :: Ord k => k -> Hoard k v (Maybe v)
hoard k = Hoard (Set.singleton k) (Map.lookup k)

-- >>> dict = Map.fromList [("foo", 10), ("bar", 20), ("baz", 100)]
-- >>> run = flip runHoard dict
-- >>> run $ sequenceA [ pure (Just 3), query "foo", query "miss", query "bar" ]
-- [Just 3,Just 10,Nothing,Just 20]
-- >>> -- hoarded keys are hidden from non-hoarder
-- >>> run $ sequenceA [ hoard "foo", query "foo"]
-- [Just 10,Nothing]
-- >>> -- hoarded keys are not hidden from other hoarder
-- >>> run $ sequenceA [ hoard "foo", hoard "foo"]
-- [Just 10,Just 10]
-- >>> -- hoarding doesn't depend on the order of effects
-- >>> run $ sequenceA [query "foo", query "bar", hoard "baz", query "foo", hoard "bar", query "baz"]
-- [Just 10,Nothing,Just 100,Just 10,Just 20,Nothing]
-- >>> -- And check my associativity!
-- >>> run $ (,) <$> sequenceA [query "foo", query "bar", hoard "baz" ] <*> sequenceA [query "foo", hoard "bar", query "baz"]
-- ([Just 10,Nothing,Just 100],[Just 10,Just 20,Nothing])
