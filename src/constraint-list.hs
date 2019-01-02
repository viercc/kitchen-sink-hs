{-# LANGUAGE GADTs, DataKinds, KindSignatures,
             InstanceSigs, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds, RankNTypes #-}
{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# LANGUAGE TypeInType #-}

import Data.Kind (Type)
import GHC.Exts (Constraint)

import Data.Constraint

-- a set of constraints
type family ManyConstraints (cs :: [Type -> Constraint])
                            (a :: Type)
                          = (r :: Constraint) where
  ManyConstraints '[] _ = ()
  ManyConstraints (c ': cs) a = (c a, ManyConstraints cs a)

-- an existential known to meet a set of constraints
data Exists :: [Type -> Constraint] -> Type where
  Exists :: (ManyConstraints cs a) => a -> Exists cs

class HasSomeC (cs :: [Type -> Constraint])
               (c :: Type -> Constraint) where
  -- Requires AllowAmbiguousTypes
  projectDict :: Dict (ManyConstraints cs a) -> Dict (c a)

instance {-# OVERLAPPING #-} HasSomeC (c ': cs) c where
  projectDict Dict = Dict

instance {-# OVERLAPPABLE #-}
         HasSomeC cs c => HasSomeC (x ': cs) c where
  projectDict Dict = projectDict @cs @c Dict

instance HasSomeC cs Show => Show (Exists cs) where
  showsPrec n ea = case ea of Exists a -> f a
    where
      f :: forall a. ManyConstraints cs a => a -> ShowS
      f a = case projectDict @cs @Show @a Dict of
              Dict -> showsPrec n a

---------------------------------

example1 :: Exists '[]
example1 = Exists id

example2 :: Exists '[Show, Eq]
example2 = Exists False

example3 :: Exists '[Eq, Eq, Ord, Ord, Show]
example3 = Exists True
