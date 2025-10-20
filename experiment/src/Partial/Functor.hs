{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Partial.Functor where

import Prelude hiding (id, (.))
import Control.Category ( Category(..) )
import Control.Arrow ( Arrow(..) )

import Witherable (Filterable(..))
import Data.Coerce ( coerce )

import Data.Functor.Const (Const(..))
import Data.Functor.Identity ( Identity(..) )
import Data.Functor.Sum (Sum(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Compose (Compose (..))
import Data.Functor.These ( These1(..) )

import Data.List.NonEmpty (NonEmpty(), nonEmpty)
import Data.Foldable (Foldable(toList))

import Partial
import Data.These (These(..))

-- * Functors from Partial to Partial

-- | Endofunctor on 'Partial'.
-- 
-- ==== Laws
--
-- - /identity/ law
--
--     @
--     'pmap' id === id
--     @
--
-- - /composition/ law
--
--     @
--     pmap (f . g) === pmap f . pmap g
--     @
--
-- - /plain functor/ law
--
--     @
--     pmap ('arr' f) === 'arr' (fmap f)
--     @
--
-- (/plain functor/ law follows from parametricity and other laws)
class Functor f => PFunctor f where
  -- | \"fmap\" but with partial functions
  pmap :: (a -? b) -> (f a -? f b)

-- | Unwrapped version of 'pmap'
partialmap :: PFunctor f => (a -> Maybe b) -> f a -> Maybe (f b)
partialmap = runPartial . pmap . Partial

-- | @f@ distributes over @Maybe@
distMaybe :: PFunctor f => f (Maybe a) -> Maybe (f a)
distMaybe = partialmap id

{-

[PFunctor laws in terms of partialmap]

identity:
  partialmap pure === pure

composition:
  partialmap (f <=< g) === partialmap f <=< partialmap g

plain functor:
  partialmap (Just . f) === Just . fmap f

[PFunctor laws in terms of distMaybe]

identity:
  distMaybe . fmap pure === pure

composition:
  distMaybe . fmap join === join . fmap distMaybe . distMaybe

-}

-- Two trivial instances:
instance PFunctor Identity where
  pmap = coerce

instance PFunctor (Const c) where
  pmap _ = Partial $ Just . coerce

-- Product, Coproduct, Smash product

-- | via 'traverse'
instance PFunctor ((,) a) where
  pmap (Partial f) = Partial $ traverse f

-- | via 'traverse'
instance PFunctor (Either a) where
  pmap (Partial f) = Partial $ traverse f

instance PFunctor (These a) where
  pmap (Partial f) = Partial $ \ab -> case ab of
    This a -> Just (This a)
    That b -> That <$> f b
    These a b -> Just $ case f b of
      Nothing -> This a
      Just b' -> These a b'

-- An instance can be made for Traversable containers...

-- | via 'traverse'
instance PFunctor Maybe where
  pmap (Partial f) = Partial $ traverse f

-- Or Filterable containers...

-- | via 'mapMaybe'
instance PFunctor [] where
  pmap (Partial f) = arr (mapMaybe f)

-- Or not any of above
instance PFunctor NonEmpty where
  pmap (Partial f) = Partial $ nonEmpty . mapMaybe f . toList

---- Constructing PFunctors ----

-- | 'Traversable'-based instance
newtype Smash t a = Smash {
    unSmash :: t a
  }
  deriving stock (Functor, Foldable, Traversable)
  deriving newtype (Applicative)

-- | 'smash' is suitable (but not the only)
--   implementation of @pmap@ for any @Traversable@ functor.
smash :: Traversable t => (a -? b) -> (t a -? t b)
smash (Partial p) = Partial (traverse p) 

instance Traversable t => PFunctor (Smash t) where
  pmap = smash

-- | 'Filterable'-based instance
newtype Filtering t a = Filtering {
    unFiltering :: t a
  }
  deriving stock (Functor, Foldable, Traversable)
  deriving newtype (Filterable)

instance Filterable t => PFunctor (Filtering t) where
  pmap (Partial f) = arr (mapMaybe f)

-- Various functor combinators

-- | Composition of PFunctors
instance (PFunctor t, PFunctor u) => PFunctor (Compose t u) where
  pmap f = arr Compose . pmap (pmap f) . arr getCompose

-- | (Pointwise) coproduct of PFunctors
instance (PFunctor t, PFunctor u) => PFunctor (Sum t u) where
  pmap f = Partial $ \case
    InL ta -> InL <$> runPartial (pmap f) ta
    InR ua -> InR <$> runPartial (pmap f) ua

-- | (Pointwise) smash product of PFunctors
instance (PFunctor t, PFunctor u) => PFunctor (Product t u) where
  pmap f = Partial $ \(Pair ta ua) -> Pair <$> runPartial (pmap f) ta <*> runPartial (pmap f) ua

-- | (Pointwise) cartesian product of two PFunctors
instance (PFunctor t, PFunctor u) => PFunctor (These1 t u) where
  pmap f = Partial $ \case
    This1 ta -> This1 <$> runPartial (pmap f) ta
    That1 ua -> That1 <$> runPartial (pmap f) ua
    These1 ta ua -> 
      let mtb = runPartial (pmap f) ta
          mub = runPartial (pmap f) ua
      in case (mtb, mub) of
           (Nothing, Nothing) -> Nothing
           (Just tb, Nothing) -> Just $ This1 tb
           (Nothing, Just ub) -> Just $ That1 ub
           (Just tb, Just ub) -> Just $ These1 tb ub