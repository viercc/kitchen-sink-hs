{-# LANGUAGE RankNTypes #-}

module QualPolyKind.A where

newtype A a = MkA (forall m. m a -> m a)
