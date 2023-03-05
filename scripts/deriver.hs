{-# language
  DeriveGeneric,
  DerivingVia,
  StandaloneDeriving,
  TypeOperators,
  FlexibleInstances,
  ScopedTypeVariables,
  TypeFamilies,
  TypeApplications,
  UndecidableInstances,
  AllowAmbiguousTypes
#-}
module Main where

import GHC.Generics hiding (D)
import Data.Coerce
import Data.Type.Coercion
import Data.Monoid (Any(..))

data D = D Bool Bool Bool Bool
    deriving (Show, Generic)

deriving via (Replaced Bool Any D)
  instance Semigroup D
deriving via (Replaced Bool Any D)
  instance Monoid D

main :: IO ()
main = do
   print (mempty :: D)
   print (D False True False True <> D False False True True)

type family Replace a b f where
    Replace a b (K1 i a) = K1 i b
    Replace a b (K1 i x) = K1 i x
    Replace a b (M1 i c f) = M1 i c (Replace a b f)
    Replace a b (f :*: g) = Replace a b f :*: Replace a b g
    Replace a b f = f

newtype Replaced a b x = Replaced x

instance (Generic x, Coercible (Rep x ()) (Replace a b (Rep x) ()), Semigroup (Replace a b (Rep x) ()))
    => Semigroup (Replaced a b x) where
    Replaced x <> Replaced y =
      let op = coerceBinOp (coercionRep @a @b @x @()) (<>)
       in Replaced $ to (from x `op` from y)

instance (Generic x, Coercible (Rep x ()) (Replace a b (Rep x) ()), Monoid (Replace a b (Rep x) ()))
    => Monoid (Replaced a b x) where
    mempty = Replaced $ to (coerceNullOp (coercionRep @a @b @x @()) mempty)

coercionRep :: forall a b x p.
    (Generic x, Coercible (Rep x p) (Replace a b (Rep x) p))
      => Coercion (Rep x p) (Replace a b (Rep x) p)
coercionRep = Coercion

coerceNullOp :: Coercion a b -> b -> a
coerceNullOp Coercion = coerce

coerceBinOp :: Coercion a b -> (b -> b -> b) -> (a -> a -> a)
coerceBinOp Coercion = coerce
