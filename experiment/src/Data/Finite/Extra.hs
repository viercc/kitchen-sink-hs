{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Finite.Extra (absurdFinite, weakenS, shiftS, shiftSRight, strengthenWithS) where

import Data.Type.Equality (type  (:~:) (Refl))
import Data.Proxy

import Data.Finite
import Data.Finite.Internal
import Data.Type.Natural
import Data.Type.Natural.Lemma.Arithmetic (plusComm, sPred')

absurdFinite :: Finite 0 -> a
absurdFinite x = x `seq` error ("absurdFinite: x = " ++ show x)

weakenS :: SNat n -> SNat k -> Finite n -> Finite (n + k)
weakenS _ _ (Finite n) = Finite n

shiftS :: SNat n -> SNat k -> Finite n -> Finite (n + k)
shiftS _ k i = withKnownNat k (shiftProxy k i)

shiftSRight :: SNat n -> SNat k -> Finite k -> Finite (n + k)
shiftSRight n k i = case plusComm k n of Refl -> withKnownNat n (shiftProxy n i)

strengthenWithS :: forall n. SNat (n + 1) -> Finite (n + 1) -> Maybe (SNat n, Finite n)
strengthenWithS n i = case withKnownNat n' (strengthen i) of
        Nothing -> Nothing
        Just i' -> Just (n', i')
    where n' = sPred' (Proxy :: Proxy n) n