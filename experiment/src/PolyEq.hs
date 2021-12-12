{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
module PolyEq where

import Type.Reflection
import Data.Type.Equality

data W
data Write

data R a = R (a -> Write)

data D f r where
    D :: C f -> C r -> D f r
    DApp :: D (a -> b) (a -> R a -> c) -> C a -> D b c
    --      ------------------------------------ 'a' is not in the output type

data C a where
  CRoot :: C W
  CNice :: (Eq a, Show a, Read a, Typeable a) => a -> C a
  CNamed :: String -> a -> C a
  CDSeal :: D a (R a) -> C a

{-
instance Eq (D f r) where
  D qf qr == D qf' qr' = qf == qf' && qr == qr'
  -- Error: Couldn't match type ‘a1’ with ‘a’ DApp bi q == DApp bi' q' = bi == bi' && q == q'

instance Eq (C a) where
  -- CRoot == CRoot = True
  -- CNice x == CNice y = x == y
  CNamed name _ == CNamed name' _ = name == name'
  CDSeal bi == CDSeal bi' = bi == bi'
-}

polyEqualsD :: D f r -> D g s -> Bool
polyEqualsD (D qf qr) (D qg qs) = polyEqualsC qf qg && polyEqualsC qr qs
polyEqualsD (DApp d qa) (DApp d' qa') = polyEqualsD d d' && polyEqualsC qa qa'
polyEqualsD _ _ = False

polyEqualsC :: C a -> C b -> Bool
polyEqualsC (CNamed name _) (CNamed name' _) = name == name'
polyEqualsC (CDSeal bi) (CDSeal bi') = polyEqualsD bi bi'
polyEqualsC (CNice a) (CNice b) = polyEq typeRep a typeRep b
polyEqualsC CRoot CRoot = True
polyEqualsC _ _ = False

polyEq :: (Eq a) => TypeRep a -> a -> TypeRep b -> b -> Bool
polyEq ta a tb b = case testEquality ta tb of
    Nothing -> False
    Just Refl -> a == b
