{-# LANGUAGE DeriveTraversable #-}
module Comonad.SingleLayer where

import Control.Comonad

data SingleLayer f a = End a | Layer a (f a)
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Functor f => Comonad (SingleLayer f) where
    extract (End a) = a
    extract (Layer a _) = a

    duplicate (End a) = End (End a)
    duplicate wa@(Layer _ fa) = Layer wa (End <$> fa)

{-

[extract (duplicate wa) = wa]
  case wa of
    End a ->
        extract (duplicate (End a)) = extract (End (End a)) = End a
    Layer a fa ->
        extract (duplicate (Layer a fa))
        = extract (Layer wa (End <$> fa))
        = wa

[fmap extract (duplicate wa) = wa]
  case wa of
    End a ->
        fmap extract (duplicate (End a)) = fmap extract (End (End a)) = End a
    Layer a fa ->
        fmap extract (duplicate (Layer a fa))
        = fmap extract (Layer wa (End <$> fa))
        = Layer (extract wa) (extract . End <$> fa)
        = Layer a fa

[duplicate (duplicate wa) = fmap duplicate (duplicate wa)]
  case wa of
    End a ->
      duplicate (duplicate wa) = End (End (End a))
         &&
      fmap duplicate (duplicate wa) = End (End (End a))
    Layer a fa ->
      duplicate (duplicate wa)
       = duplicate (Layer wa (End <$> fa))
       = Layer (Layer wa (End <$> fa)) (End . End <$> fa)
          &&
      fmap duplicate (duplicate wa)
       = fmap duplicate (Layer wa (End <$> fa))
       = Layer (Layer wa (End <$> fa)) (duplicate . End <$> fa)
       = Layer (Layer wa (End <$> fa)) (End . End <$> fa) 

-}