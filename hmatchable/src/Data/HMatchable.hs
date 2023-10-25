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
import Data.Type.Equality((:~:)(..))
import Data.GADT.Show ( GShow(..) )
import Data.GADT.Compare (GEq(..))

import Data.HFunctor (HFunctor(..))
import Data.HFunctor.HTraversable (HTraversable(..), hfoldMap)

import Data.HFree
import Data.HFix

type  HMatchable :: ((k -> Type) -> k -> Type) -> Constraint
class (HFunctor t) => HMatchable t where
  hzipMatchWith :: (forall xx. f xx -> g xx -> Maybe (h xx)) ->
                   t f yy -> t g yy -> Maybe (t h yy)

-----

infix 1 :==
data Assignment tag f where
  (:==) :: tag a -> f a -> Assignment tag f

instance (GShow tag, GShow f) => Show (Assignment tag f) where
  showsPrec p (tag :== f) = showParen (p < 1) $ gshowsPrec 1 tag . (" :== " ++) . gshowsPrec 1 f

dlookup :: (GEq tag) => tag a -> [Assignment tag f] -> Maybe (f a)
dlookup _    [] = Nothing
dlookup taga ( (tagb :== fb) : rest) =
  case geq taga tagb of
    Just Refl -> Just fb
    Nothing   -> dlookup taga rest

-----------------------------------------------

hPatternMatch :: (HTraversable t, HMatchable t) =>
  HFree t var a -> HFix t a -> Maybe [Assignment var (HFix t)]
hPatternMatch (HPure var) val = Just [var :== val]
hPatternMatch (HFree tpat) (HFix tvalue) = hfoldMap getConst <$> hzipMatchWith (\pat val -> Const <$> hPatternMatch pat val) tpat tvalue
