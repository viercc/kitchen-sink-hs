{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
module Polynomial where

import Data.Kind (Type)
import Data.Void
import GHC.Generics

data Poly tag x where
  P :: tag r -> (r -> x) -> Poly tag x

deriving instance Functor (Poly tag)

class Polynomial f where
  type family Tag f :: Type -> Type

  toPoly :: f x -> Poly (Tag f) x
  fromPoly :: Poly (Tag f) x -> f x


data TagA r x where
  TagA :: TagA r r

instance Polynomial ((->) r) where
  type Tag ((->) r) = TagA r
  
  toPoly f = P TagA f
  fromPoly (P TagA f) = f

absurdV1 :: V1 a -> any
absurdV1 v1 = case v1 of

instance Polynomial V1 where
  type Tag V1 = V1
  toPoly = absurdV1
  fromPoly (P tag _)= absurdV1 tag

data TagK c x where
  TagK :: c -> TagK c Void

instance Polynomial U1 where
  type Tag U1 = TagK ()

  toPoly _ = P (TagK ()) absurd
  fromPoly _ = U1

instance Polynomial (K1 i c) where
  type Tag (K1 i c) = TagK c

  toPoly (K1 c) = P (TagK c) absurd
  fromPoly (P (TagK c) _) = K1 c



data Tag1 x where
  Tag1 :: Tag1 ()

instance Polynomial Par1 where
  type Tag Par1 = Tag1

  toPoly (Par1 x) = P Tag1 (const x)
  fromPoly (P Tag1 x') = Par1 (x' ())


instance (Polynomial f, Polynomial g) => Polynomial (f :+: g) where
  type Tag (f :+: g) = (Tag f :+: Tag g)

  toPoly (L1 fx) = case toPoly fx of
    P tag rep -> P (L1 tag) rep
  toPoly (R1 gx) = case toPoly gx of
    P tag rep -> P (R1 tag) rep

  fromPoly (P (L1 tag) rep) = L1 (fromPoly (P tag rep))
  fromPoly (P (R1 tag) rep) = R1 (fromPoly (P tag rep))


data TagMul f g x where
  TagMul :: f x -> g y -> TagMul f g (Either x y)

instance (Polynomial f, Polynomial g) => Polynomial (f :*: g) where
  type Tag (f :*: g) = TagMul (Tag f) (Tag g)

  toPoly (fx :*: gx) =
    case (toPoly fx, toPoly gx) of
      (P tagF repF, P tagG repG) ->
        P (TagMul tagF tagG) (either repF repG)

  fromPoly (P (TagMul tagF tagG) rep) =
    fromPoly (P tagF (rep . Left)) :*: fromPoly (P tagG (rep . Right))

{-
data TagComp f g r where
  TagComp :: Reifies tagFn (x -> Exists g) => f x -> Proxy tagFn -> TagComp f g (DSum x tagFn)

data Exists f where Ex :: f a -> Exists f

data DSum x tagFn where
  DSum :: x -> Proxy tagFn -> (forall h. Reifies tagFn (x -> Exists h) => (h y, y)) -> DSum x tagFn

instance (Polynomial f, Polynomial g) => Polynomial (f :.: g) where
  type Tag (f :.: g) = TagComp (Tag f) (Tag g)
  
  toPoly (Comp1 fgy) = case toPoly fgy of
    P tagF repF ->
      let getTag x = case toPoly (repF x) of P tagG _ -> Ex tagG
          rep (DSum x tagFnName (_, y)) ->
            case toPoly (repF x) of
      in reify getTag $ \tagFnName -> TagComp tagF tagFnName

  fromPoly (P (TagComp tagF tagFnName) rep) =
    let repF x =
          case reflect tagFnName x of
            Ex tagG -> fromPoly $ P tagG (\y -> rep $ DSum x tagFnName (tagG, y))
    in Comp1 $ fromPoly (P tagF repF)
-}
