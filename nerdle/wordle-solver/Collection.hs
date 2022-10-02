{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
module Collection(Finite(..), Collection(..), VectorIx(..), withCollection) where

import Data.Coerce
import Data.Reflection
import Data.Proxy

import Data.Vector (Vector)
import Data.Vector qualified as V

import Data.Set (Set)
import Data.Set qualified as Set

class (Ord x) => Finite x where
    universe :: Set x

class (Finite ix, Show ix) => Collection a ix | ix -> a where
    itemId :: ix -> Int
    itemValue :: ix -> a

newtype VectorIx a name = VectorIx Int
    deriving stock (Eq, Ord)
    deriving newtype Show

instance Reifies name (Vector a) => Finite (VectorIx a name) where
    universe = Set.fromDistinctAscList (VectorIx <$> [0 .. n - 1])
      where
        n = V.length (reflect (Proxy :: Proxy name))

instance Reifies name (Vector a) => Collection a (VectorIx a name) where
    itemId = coerce
    itemValue (VectorIx i) = V.unsafeIndex (reflect (Proxy :: Proxy name)) i

universeOfName :: Reifies name (Vector a) => Proxy name -> Set (VectorIx a name)
universeOfName _ = universe

withCollection :: Vector a -> (forall ix. Collection a ix => Set ix -> r) -> r
withCollection values body = reify values (\name -> body (universeOfName name))