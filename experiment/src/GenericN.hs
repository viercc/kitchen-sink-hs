{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module GenericN where

import Data.Kind
--import GHC.TypeLits

data CMeta = CMeta -- Constructor metadata
data FMeta = FMeta -- Field metadata

data DataRep a = Constructor CMeta (ConstrRep a)
               | DataRep a :+: DataRep a

data ConstrRep a = Field FMeta (Term a)
                 | ConstrRep a :*: ConstrRep a

data Term a where
  I :: Term (a -> a)
  K :: Term (a -> b -> a)
  S :: Term ((a -> b -> c) -> (a -> b) -> a -> c)
  B :: Term ((b -> c) -> (a -> b) -> a -> c)
  C :: Term ((a -> b -> c) -> b -> a -> c)
  (:$) :: Term (a -> b) -> Term a -> Term b
  Lift :: a -> Term a

infixl 8 :$

type family Reduce (a :: Term k) :: Maybe (Term k) where
  Reduce (I :$ a) = Just a
  Reduce (K :$ a :$ b) = Just a
  Reduce (B :$ a :$ b :$ c) = Just (a :$ (b :$ c))
  Reduce (C :$ a :$ b :$ c) = Just (a :$ c :$ b)
  Reduce (S :$ a :$ b :$ c) = Just (a :$ c :$ (b :$ c))
  Reduce (Lift f :$ Lift a) = Just (Lift (f a))
  Reduce (f :$ x) = ReduceAux f x (Reduce f) (Reduce x)
  Reduce a = Nothing

type family ReduceAux (f :: Term (j -> k)) (x :: Term j)
                      (f' :: Maybe (Term (j -> k)))
                      (k' :: Maybe (Term j)) :: Maybe (Term k)
  where
    ReduceAux f x Nothing   Nothing   = Nothing
    ReduceAux f x (Just f') Nothing   = Just (f' :$ x)
    ReduceAux f x Nothing   (Just x') = Just (f :$ x')
    ReduceAux f x (Just f') (Just x') = Just (f' :$ x')

type NF x = NFLoop x (Reduce x)

type family NFLoop (a :: Term k) (ma' :: Maybe (Term k)) :: Term k where
  NFLoop a Nothing   = a
  NFLoop a (Just a') = NFLoop a' (Reduce a')

type Eval0 (x :: Term Type) = Eval0' (NF x)

data family Eval0' (x :: Term Type) :: Type
newtype instance Eval0' (Lift a) = Eval0 a

type Eval1 (x :: Term (Type -> Type)) = Eval1' (NF x)
data family Eval1' (f :: Term (Type -> Type)) :: Type -> Type

newtype instance Eval1' I             a = Id1 a
newtype instance Eval1' (K :$ Lift c) a = K1 c
newtype instance Eval1' (B :$ f :$ g) a = B1 (Eval1' f (Eval1' g a))
newtype instance Eval1' (C :$ f :$ b) a = C1 (Eval2' f a (Eval0' b))
newtype instance Eval1' (S :$ f :$ g) a = S1 (Eval2' f a (Eval1' g a))
newtype instance Eval1' (Lift f)      a = Lift1 (f a)

type Eval2 (x :: Term (Type -> Type -> Type)) = Eval2' (NF x)
data family Eval2' (f :: Term (Type -> Type -> Type)) :: Type -> Type -> Type

newtype instance Eval2' K        a b      = K2 a
newtype instance Eval2' (K :$ f) a b      = Kf2 (Eval1' f b)
newtype instance Eval2' (C :$ f) a b      = C2 (Eval2' f b a)
newtype instance Eval2' (B :$ f :$ g) a b = B2 (Eval2' f (Eval1' g a) b)
newtype instance Eval2' (S :$ f :$ g) a b = S2 (Eval3' f a (Eval1' g a) b) 
newtype instance Eval2' (Lift f) a b      = Lift2 (f a b)

data family Eval3' (f :: Term (Type -> Type -> Type -> Type))
              :: Type -> Type -> Type -> Type

newtype instance Eval3' (K :$ f) a b c = Kf3 (Eval2' f b c)
newtype instance Eval3' (C :$ f) a b c = C3 (Eval3' f b a c)
newtype instance Eval3' (B :$ f :$ g) a b c = B3 (Eval3' f (Eval1' g a) b c)
-- newtype instance Eval3' (S :$ f :$ g) a b c = S3 (Eval4' f a (Eval1' g a) b c)
newtype instance Eval3' (Lift f) a b c = Lift3 (f a b c)

{-

type F a b = (a -> b) -> a

F a b = (->) ((->) a b) a
F a b = C (->) a ((->) a b)
F a b = B (C (->) a) ((->) a) b
F a = B (C (->) a) ((->) a)
F a = S (\a -> B (C (->) a)) (->) a
F a = S (B B (C (->))) (->) a
F = S (B B (C (->))) (->)

Eval2' (S (B B (C (->))) (->)) a b
= Eval3' (B B (C (->))) a (Eval1' (->) a) b
                          ~~~~~~~~~~~~~~~
-}
