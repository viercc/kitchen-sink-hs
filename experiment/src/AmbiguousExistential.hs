{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module AmbiguousExistential where

import Data.Proxy

-- Ambiguous type
data Foo = forall a. (Bounded a, Show a) => Foo

useFoo :: Foo -> (forall a. (Bounded a, Show a) => Proxy a -> r) -> r
useFoo (Foo @a) k = k @a Proxy -- since GHC 9.2

showMinMax :: forall a. (Bounded a, Show a) => Proxy a -> String
showMinMax _ = show (minBound :: a, maxBound :: a)

showFoo :: Foo -> String
showFoo foo = useFoo foo showMinMax
