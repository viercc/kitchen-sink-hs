{-# LANGUAGE RankNTypes #-}
module QualPolyKindA where

newtype A a = MkA (forall m. m a -> m a)
