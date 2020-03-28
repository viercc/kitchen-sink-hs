{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
module Cats where

import           Control.Category
import           Prelude          hiding (Functor (..), fst, id, map, snd, (.))
import qualified Prelude

import           Control.Monad    ((<=<))

import           Data.Map         (Map)
import qualified Data.Map         as Map
import qualified Data.Maybe

import           Data.Void
import qualified Data.Align
import           Data.These

newtype Partial a b = Partial (a -> Maybe b)

instance Category Partial where
    id = Partial return
    Partial f . Partial g = Partial (f <=< g)

type Hask = (->)

---- Functor ----

class (Category (Dom f), Category (Cod f)) => Functor (f :: j -> k) where
    type Dom f :: j -> j -> *
    type Cod f :: k -> k -> *

    map :: Dom f x y -> Cod f (f x) (f y)

    -- map id = id
    -- map (f . g) = map f . map g

newtype HaskF f a = HaskF (f a)

instance (Prelude.Functor f) => Functor (HaskF f) where
    type Dom (HaskF f) = Hask
    type Cod (HaskF f) = Hask

    map f (HaskF x) =HaskF (Prelude.fmap f x)

instance Functor [] where
    type Dom [] = Partial
    type Cod [] = Hask

    map (Partial f) = Data.Maybe.mapMaybe f

instance (Ord k) => Functor (Map k) where
    type Dom (Map k) = Partial
    type Cod (Map k) = Hask

    map (Partial f) = Map.mapMaybe f

---- CartesianProduct ----

class Category cat => CartesianProduct (cat :: k -> k -> *) where
    type CP cat :: k -> k -> k
    type Terminal cat :: k

    fst :: cat (CP cat a b) a
    snd :: cat (CP cat a b) b
    (&&&) :: cat a x -> cat a y -> cat a (CP cat x y)
    term :: cat a (Terminal cat)

    -- fst . (f &&& g) = f
    -- snd . (f &&& g) = g
    -- (fst . f) &&& (snd . f) = f
    -- term is unique morphism (forall f :: cat a (Terminal cat), f = term)

(***) :: (CartesianProduct cat, p ~ CP cat)
      => cat x x' -> cat y y' -> cat (p x y) (p x' y')
f *** g = (f . fst) &&& (g . snd)

assoc :: (CartesianProduct cat, p ~ CP cat)
      => cat (p x (p y z)) (p (p x y) z)
assoc = (fst &&& (fst . snd)) &&& (snd . snd)

instance CartesianProduct Hask where
  type CP Hask = (,)
  type Terminal Hask = ()

  fst :: (x, y) -> x
  fst = Prelude.fst

  snd :: (x, y) -> y
  snd = Prelude.snd

  term :: a -> ()
  term = const ()
  
  (&&&) :: (a -> x) -> (a -> y) -> (a -> (x, y))
  (&&&) f g a = (f a, g a)

instance CartesianProduct Partial where
  type CP Partial = These
  type Terminal Partial = Void
  
  fst :: Partial (These x y) x
  fst = Partial $ \case
    This x -> Just x
    That _ -> Nothing
    These x _ -> Just x

  snd :: Partial (These x y) y
  snd = Partial $ \case
    This _ -> Nothing
    That y -> Just y
    These _ y -> Just y

  term :: Partial a Void
  term = Partial (const Nothing)

  (&&&) :: Partial a x -> Partial a y -> Partial a (These x y)
  Partial f &&& Partial g = Partial $ \a -> pairMaybes (f a) (g a)

pairMaybes :: Maybe a -> Maybe b -> Maybe (These a b)
pairMaybes Nothing  Nothing = Nothing
pairMaybes (Just x) Nothing = Just (This x)
pairMaybes Nothing  (Just y) = Just (That y)
pairMaybes (Just x) (Just y) = Just (These x y)

---- (Cartesian) lax monoidal functors ----

class (Functor f, CartesianProduct (Dom f), CartesianProduct (Cod f))
      => LaxMonoidal f where
  unit :: Cod f (Terminal (Cod f)) (f (Terminal (Dom f)))
  multiply :: Cod f (CP (Cod f) (f a) (f b)) (f (CP (Dom f) a b))

  -- [Naturailty] multiply . (map f *** map g) = map (f *** g) . multiply
  -- [Left Unit]  map snd . multiply . (unit . term) &&& id = id
  -- [Right Unit] map fst . multiply . (id &&& (unit . term)) = id
  -- [Associativity] map assoc . multiply . (id *** multiply) = multiply . (multiply *** id) . assoc

instance (Applicative f) => LaxMonoidal (HaskF f) where
  unit :: () -> HaskF f ()
  unit = HaskF . pure

  multiply :: (HaskF f a, HaskF f b) -> HaskF f (a,b)
  multiply (HaskF x, HaskF y) = HaskF ((,) <$> x <*> y)

instance (Ord k) => LaxMonoidal (Map k) where
  unit :: () -> Map k Void
  unit _ = Data.Align.nil

  multiply :: (Map k a, Map k b) -> Map k (These a b)
  multiply = uncurry Data.Align.align

{-

-- This instance is not lawful
instance LaxMonoidal [] where
  unit _ = Data.Align.nil
  multiply = uncurry Data.Align.align

-}
