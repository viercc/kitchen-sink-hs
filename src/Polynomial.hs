{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
module Polynomial where

import Data.Proxy
import Data.Reflection

import GHC.Generics

data Poly tag x where
  P :: tag r -> (r -> x) -> Poly tag x

deriving instance Functor (Poly tag)

class Polynomial f where
  type family Tag f :: * -> *

  toPoly :: f x -> Poly (Tag f) x
  fromPoly :: Poly (Tag f) x -> f x


data TagA r x where
  TagA :: TagA r r

instance Polynomial ((->) r) where
  type Tag ((->) r) = TagA r
  
  toPoly f = P TagA f
  fromPoly (P TagA f) = f


instance Polynomial V1 where
  type Tag V1 = V1


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

  toPoly (Par1 x) = P _ (const x)
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
  type Tag (f :*: g) = TagMul f g

  toPoly (fx :*: gx) =
    let P tagF repF = toPoly fx
        P tagG repG = toPoly gx
    in P (TagMul tagF tagG) (either repF repG)

  fromPoly (P (TagMul tagF tagG) rep) =
    fromPoly tagF (rep . Left) :*: fromPoly tagG (rep . Right)


instance (Polynomial f, Polynomial g) => Polynomial (f :.: g) where
  ???????????????????????????????????
