{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Matrix.Fold
  ( MatExprF (..),
    zeroE,
    denseE,
    addE,
    multE,
    evalMatExpr,
  )
where

import Data.Kind (Type)
import GHC.TypeLits (KnownNat, Nat)
import Matrix.Sized

type Mat = Nat -> Nat -> Type

type (f :: Mat) ~> (g :: Mat) =
  forall m n. (KnownNat m, KnownNat n) => f m n -> g m n

class Functor' (f :: Mat -> Mat) where
  fmap' :: (a ~> b) -> (f a ~> f b)

-- Algebra is arrow f a to a
type Algebra' f a = f a ~> a

-- Fixpoint of endofunctor on (Nat -> Nat -> *)
type Fix' :: (Mat -> Mat) -> Mat
newtype Fix' f m n
  = Fix' {unFix' :: f (Fix' f) m n}

-- Catamorphism
cata' :: (Functor' f) => Algebra' f a -> (Fix' f ~> a)
cata' phi = phi . fmap' (cata' phi) . unFix'

type MatExprF :: Type -> Mat -> Mat
data MatExprF k (r :: Mat) m n where
  Zero :: MatExprF k r m n
  Dense :: Matrix m n k -> MatExprF k r m n
  Add :: r m n -> r m n -> MatExprF k r m n
  Mult :: (KnownNat p) => r m p -> r p n -> MatExprF k r m n

zeroE :: MatExpr k m n
zeroE = Fix' Zero

denseE :: Matrix m n k -> MatExpr k m n
denseE = Fix' . Dense

addE :: MatExpr k m n -> MatExpr k m n -> MatExpr k m n
addE a b = Fix' (Add a b)

multE :: (KnownNat n) => MatExpr k m n -> MatExpr k n p -> MatExpr k m p
multE a b = Fix' (Mult a b)

instance Functor' (MatExprF k) where
  fmap' _ Zero = Zero
  fmap' _ (Dense m) = Dense m
  fmap' f (Add m1 m2) = Add (f m1) (f m2)
  fmap' f (Mult m1 m2) = Mult (f m1) (f m2)

type MatExpr k = Fix' (MatExprF k)

newtype Matrix' k m n = Wrap (Matrix m n k)

evalAlg :: (Ring k) => Algebra' (MatExprF k) (Matrix' k)
evalAlg Zero = Wrap zeroMat
evalAlg (Dense m) = Wrap m
evalAlg (Add (Wrap m1) (Wrap m2)) = Wrap (plus m1 m2)
evalAlg (Mult (Wrap m1) (Wrap m2)) = Wrap (multMat m1 m2)

evalMatExpr ::
  forall k m n.
  (Ring k, KnownNat m, KnownNat n) =>
  MatExpr k m n -> Matrix m n k
evalMatExpr expr = case cata' evalAlg expr of Wrap mat -> mat
