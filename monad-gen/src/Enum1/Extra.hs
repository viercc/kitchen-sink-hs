{-# LANGUAGE ScopedTypeVariables, TypeOperators, TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
module Enum1.Extra(
  skolem, skolem2, skolem3,
  
  allNaturals,
  allPures,
  allJoins,
  allLiftA2,

  Template(),
  enumTemplates,
  runTemplate
) where

import Data.Kind

import Control.Applicative (liftA2)
import Control.Monad.State
import Data.Functor.Identity

import GHC.Generics

import Vec
import Util
import Enum1

skolem :: forall m. (Traversable m, Enum1 m) => Vec (m Int)
skolem = fmap fillIn $ enum1 $ vec [state (\i -> (i, i+1))]
  where fillIn mx = evalState (sequenceA mx) 0

skolem2 :: forall m. (Traversable m, Enum1 m) => Vec (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (Traversable m, Enum1 m) => Vec (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

-----------------------------------

newtype Template (f :: Type -> Type) g = MkTemplate (Vec (Int, g ()))

enumTemplates
  :: forall f g.
     (Enum1 f, CoEnum1 f, Enum1 g)
  => Vec (Template f g)
enumTemplates = coerceMap MkTemplate (traverse entry fs)
  where
    fs = enum1 @f (singleton ())
    gs = enum1 @g (singleton ())
    entry f1 = fmap (holeCount f1, ) gs

runTemplate
  :: forall f g a.
     (Enum1 f, CoEnum1 f, Traversable g)
  => Template f g
  -> Vec (f a -> g a)
runTemplate (MkTemplate t) = toNat <$> traverse inner t
  where
    inner (n, g1) =
      let vars = generate n id
      in traverse (const vars) g1
    toNat table fa =
      let args = toVec fa
          gi = table ! fromEnum1 @f 1 (const 0) fa
      in (args !) <$> gi

------------------------------------------

allNaturals :: forall f g a. (CoEnum1 f, Enum1 g) => Vec (f a -> g a)
allNaturals = coenum1 enum1

allPures :: forall f a. (Enum1 f) => Vec (a -> f a)
allPures = coerceMap (. Identity) $ allNaturals @Identity @f

allJoins :: forall f a. (Functor f, CoEnum1 f, Enum1 f) => Vec (f (f a) -> f a)
allJoins = coerceMap (. Comp1) $ allNaturals @(f :.: f) @f

allLiftA2 :: forall f a b c. (Functor f, CoEnum1 f, Enum1 f) => (a -> b -> c) -> Vec (f a -> f b -> f c)
allLiftA2 f = coenum1 $ \as -> coenum1 $ \bs -> enum1 (liftA2 f as bs)
