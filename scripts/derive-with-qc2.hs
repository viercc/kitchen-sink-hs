#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import Data.Coerce
import Data.Monoid (Ap(..), Any(..))

newtype CatProd c d a b = CatProd (c a b, d a b)

instance (Category c, Category d) => Category (CatProd c d) where
  id = CatProd (id, id)
  CatProd (f, f') . CatProd (g, g') = CatProd (f . g, f' . g')

instance (Arrow c, Arrow d) => Arrow (CatProd c d) where
  arr f = CatProd (arr f, arr f)
  first (CatProd (f, f')) = CatProd (first f, first f')

newtype Mon m a b = Mon m

instance Monoid m => Category (Mon m) where
  id = Mon mempty
  Mon x . Mon y = Mon (x <> y)

instance Monoid m => Arrow (Mon m) where
  arr _ = Mon mempty
  first (Mon x) = Mon x

newtype Build m i o =
    Build (m Bool, i -> m o)

--    deriving (Category) via (CatProd (Mon (Ap m Any)) (Kleisli m))

deriving via (CatProd (Mon (Ap m Any)) (Kleisli m))
  instance (Monad m, forall x y. Coercible x y => Coercible (m x) (m y))
    => Category (Build m)

deriving via (CatProd (Mon (Ap m Any)) (Kleisli m))
  instance (Monad m, forall x y. Coercible x y => Coercible (m x) (m y))
    => Arrow (Build m)

main :: IO ()
main = putStrLn "Ok"

