{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module QualPolyKind.B where

import Data.Kind (Type)
import QualPolyKind.A

-- MkB :: forall k (a :: k). (forall (m :: k -> *). m a -> m a) -> B a
newtype B a = MkB (forall m. m a -> m a)

fooA :: forall (a :: Type). (forall m. m a -> m a) -> ()
-- If the type annotation lacks the kind of @a@, like:
--
-- > fooA :: forall a. (forall m. m a -> m a) -> ()
--
-- it will mean below
--
-- > fooA :: forall k (a :: k). (forall (m :: k -> *). m a -> m a) -> ()
--
-- and this doesn't typecheck.
fooA f =
  let _xx :: A a
      _xx = MkA f
   in ()

-- fooB :: forall k (a :: k). (forall (m :: k -> *). m a -> m a) -> ()
fooB :: forall a. (forall m. m a -> m a) -> ()
fooB f =
  let _xx :: B a
      _xx = MkB f
   in ()
