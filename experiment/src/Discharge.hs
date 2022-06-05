-- <https://mail.haskell.org/pipermail/haskell-cafe/2022-April/135224.html>

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds, PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Discharge where

import GHC.TypeNats
import Data.Proxy
import Data.Kind

class KnownNat n => F (n :: Nat)

foo :: forall n. F n => (F n => Proxy n -> Proxy n) -> Int
foo f = let _ = f (Proxy @n) in 0

class (KnownNat n, 1 <= n) => G (n :: Nat)

bar :: forall n. G n => (G n => Proxy n -> Proxy n) -> Int
bar f = let _ = f (Proxy @n) in 0

type family X (n :: Nat) :: Bool where
    X 0 = 'False
    X n = 'True

class (X n ~ 'True) => H (n :: Nat)

baz :: forall n. H n => (H n => Proxy n -> Proxy n) -> Int
baz f = let _ = f (Proxy @n) in 0
