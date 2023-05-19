{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BlockArguments #-}
module Preco where

import Control.Monad
import Control.Comonad

newtype Preco f r a = Preco { runPreco :: f (a -> r) -> r }

instance Functor f => Functor (Preco f r) where
    fmap g (Preco c) = Preco (c . fmap (. g))

instance Comonad f => Applicative (Preco f r) where
    pure a = Preco \far -> extract far a
    (<*>) = ap

instance Comonad f => Monad (Preco f r) where
    ma >>= k = joinCo $ fmap k ma

joinCo :: Comonad f => Preco f r (Preco f r a) -> Preco f r a
joinCo mma = Preco $ runPreco mma . extend (flip runPreco)
