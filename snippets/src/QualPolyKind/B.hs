    {-# LANGUAGE RankNTypes, ScopedTypeVariables, PolyKinds #-}
    module QualPolyKind.B where

    import QualPolyKind.A

    -- MkB :: forall k (a :: k). (forall (m :: k -> *). m a -> m a) -> B a
    newtype B a = MkB (forall m. m a -> m a)

    -- fooA :: forall k (a :: k). (forall (m :: k -> *). m a -> m a) -> ()
    fooA :: forall a. (forall m. m a -> m a) -> ()
    fooA f =
      let xx :: A a
          xx = MkA f
      in ()

    -- fooB :: forall k (a :: k). (forall (m :: k -> *). m a -> m a) -> ()
    fooB :: forall a. (forall m. m a -> m a) -> ()
    fooB f =
      let xx :: B a
          xx = MkB f
      in ()
