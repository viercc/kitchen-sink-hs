{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.HFree where

import Data.Kind (Type)

import Data.Functor.Classes(showsUnaryWith)

import Data.GADT.Show ( GShow(..) )

import Data.HFunctor (HFunctor(..))
import Data.HFunctor.HTraversable (HTraversable(..))

type HFree :: ((k -> Type) -> k -> Type) -> (k -> Type) -> k -> Type
data HFree t f a
  = HPure (f a)
  | HFree (t (HFree t f) a)

instance (HFunctor t) => HFunctor (HFree t) where
    hmap fg (HPure f) = HPure (fg f)
    hmap fg (HFree tm) = HFree (hmap (hmap fg) tm)

instance (HTraversable t) => HTraversable (HFree t) where
    htraverse k (HPure f) = HPure <$> k f
    htraverse k (HFree tm) = HFree <$> htraverse (htraverse k) tm

instance (GShow f, GShow (t (HFree t f))) => GShow (HFree t f) where
  gshowsPrec p (HPure fa) = showsUnaryWith gshowsPrec "HPure" p fa
  gshowsPrec p (HFree tfa) = showsUnaryWith gshowsPrec "HFree" p tfa

instance (GShow f, GShow (t (HFree t f))) => Show (HFree t f a) where
  showsPrec = gshowsPrec

