{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
module Monad.Ranked(
  Ranked(..)
) where

import Control.Applicative

newtype Ranked f a = Ranked [f a]
  deriving (Show, Read, Eq, Ord, Functor, Foldable)

instance (Alternative f) => Applicative (Ranked f) where
  pure a = Ranked [pure a]
  Ranked [] <*> _         = Ranked []
  _         <*> Ranked [] = Ranked []
  Ranked (fa : fas) <*> Ranked (fb : fbs)
    = let fc = fa <*> fb
          fcs = map (fa <*>) fbs
          Ranked fds = Ranked fcs <|> Ranked fas <*> Ranked fbs
      in Ranked $ fc : fds

instance (Alternative f) => Alternative (Ranked f) where
  empty = Ranked $ pure empty
  Ranked fas  <|> Ranked fbs = Ranked $ go fas fbs
    where go [] fys = fys
          go fxs [] = fxs
          go (fx:fxs) (fy:fys) = (fx <|> fy) : go fxs fys
