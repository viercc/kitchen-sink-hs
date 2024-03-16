{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.HMatchable where

import Data.Kind (Type, Constraint)

import Data.Functor.Const
import Data.GADT.Compare (GCompare)

import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)

import Data.HFunctor (HFunctor(..))
import Data.HFunctor.HTraversable (HTraversable(..), hfoldMap)

import Data.Functor.Combinator(HFree(..))

import Data.HFix

type  HMatchable :: ((k -> Type) -> k -> Type) -> Constraint
class (HFunctor t) => HMatchable t where
  hzipMatchWith :: (forall xx. f xx -> g xx -> Maybe (h xx)) ->
                   t f yy -> t g yy -> Maybe (t h yy)

hPatternMatchWith :: (HTraversable t, HMatchable t, Monoid m)
  => (forall k. var k -> HFix t k -> m)
  -> HFree t var a -> HFix t a -> Maybe m
hPatternMatchWith p (HReturn var) val = Just (p var val)
hPatternMatchWith p (HJoin tpat) (HFix tvalue) = hfoldMap getConst <$> hzipMatchWith (\pat val -> Const <$> hPatternMatchWith p pat val) tpat tvalue

hPatternMatch :: (GCompare var, HTraversable t, HMatchable t)
  => HFree t var a -> HFix t a -> Maybe (DMap var (HFix t))
hPatternMatch = hPatternMatchWith DMap.singleton