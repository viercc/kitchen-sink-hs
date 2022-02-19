{-# LANGUAGE
  QuantifiedConstraints,
  DerivingVia,
  DerivingStrategies,
  DeriveTraversable,
  StandaloneDeriving,
  
  PolyKinds,
  
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  
  InstanceSigs,
  TypeOperators,
  TupleSections
#-}
module FMonad.Compose(
    module FMonad,

    ComposePost,
    ComposePre(..),
    ComposeBoth(..)
) where

import Data.Kind (Type)
import Control.Applicative (Alternative)
import Control.Monad (join)
import Data.Functor.Classes ( Eq1, Ord1 )

import Data.Functor.Compose

import FMonad

-- | Just there for the symmetry of names
type ComposePost = Compose

-- de-PolyKind-ing of Compose
type (:.:) :: (Type -> Type) -> (Type -> Type) -> Type -> Type
type (:.:) = Compose

-- | Flipped-order Compose.
--   
-- @ComposePre f@ can be a 'FMonad' in the similar way 'ComposePost' is.
-- 
-- The only difference is @ComposePre f@ composes @f@ to the right (_pre_compose)
-- compared to @ComposePost f@ which composes to the left (_post_compose).
type    ComposePre :: (j -> k) -> (k -> Type) -> j -> Type
newtype ComposePre f g a = ComposePre { getComposePre :: g (f a) }
    deriving stock (Show, Read, Functor, Foldable)

deriving stock instance (Traversable f, Traversable g) => Traversable (ComposePre f g)

deriving via ((g :.: f) a)
  instance (Eq1 f, Eq1 g, Eq a) => Eq (ComposePre f g a)

deriving via ((g :.: f) a)
  instance (Ord1 f, Ord1 g, Ord a) => Ord (ComposePre f g a)

deriving via (g :.: f)
  instance (Eq1 f, Eq1 g) => Eq1 (ComposePre f g)

deriving via (g :.: f)
  instance (Ord1 f, Ord1 g) => Ord1 (ComposePre f g)

deriving via (g :.: f)
  instance (Applicative f, Applicative g) => Applicative (ComposePre f g)

deriving via (g :.: f)
  instance (Applicative f, Alternative g) => Alternative (ComposePre f g)

instance Functor f => FFunctor (ComposePre f) where
  ffmap gh = ComposePre . gh . getComposePre

instance Monad f => FMonad (ComposePre f) where
  fpure = ComposePre . fmap return
  fjoin = ComposePre . fmap join . getComposePre . getComposePre

-- | Both-side composition of Monad.
--   
-- @ComposeBoth f g@ can be a 'FMonad' in the similar way 'ComposePost' and 'ComposePre' is.
-- 
-- The only difference is @ComposeBoth f@ composes @f@ to the right (_pre_compose)
-- compared to @Compose f@ which composes to the left (_post_compose).
type    ComposeBoth :: (k2 -> Type) -> (k0 -> k1) -> (k1 -> k2) -> k0 -> Type
newtype ComposeBoth f g h a = ComposeBoth { getComposeBoth :: f (h (g a)) }
    deriving stock (Show, Read, Functor, Foldable)

deriving stock
  instance (Traversable f, Traversable g, Traversable h) => Traversable (ComposeBoth f g h)

deriving via ((f :.: h :.: g) a)
  instance (Eq1 f, Eq1 g, Eq1 h, Eq a) => Eq (ComposeBoth f g h a)

deriving via ((f :.: h :.: g) a)
  instance (Ord1 f, Ord1 g, Ord1 h, Ord a) => Ord (ComposeBoth f g h a)

deriving via (f :.: h :.: g)
  instance (Applicative f, Applicative g, Applicative h) => Applicative (ComposeBoth f g h)

deriving via (f :.: h :.: g)
  instance (Alternative f, Alternative g, Applicative h) => Alternative (ComposeBoth f g h)

instance (Functor f, Functor g) => FFunctor (ComposeBoth f g) where
  ffmap gh = ComposeBoth . fmap gh . getComposeBoth

instance (Monad f, Monad g) => FMonad (ComposeBoth f g) where
  fpure = ComposeBoth . return . fmap return
  fjoin = ComposeBoth . fmap (fmap join) . join . fmap getComposeBoth . getComposeBoth