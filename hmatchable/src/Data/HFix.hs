{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.HFix where

import Data.Functor.Classes(showsUnaryWith)

import Data.Kind (Type)

import Data.GADT.Show ( GShow(..) )

type HFix :: ((k -> Type) -> k -> Type) -> k -> Type
newtype HFix t a = HFix (t (HFix t) a)

instance GShow (t (HFix t)) => GShow (HFix t) where
  gshowsPrec p (HFix tt) = showsUnaryWith gshowsPrec "HFix" p tt

instance GShow (t (HFix t)) => Show (HFix t a) where
  showsPrec = gshowsPrec
