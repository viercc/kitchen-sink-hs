{-# LANGUAGE TypeOperators #-}
module Rank2Unzip where

import qualified Rank2
import Rank2 (Only(..))
import GHC.Generics
import Data.Functor.Identity

type Pair a b = Only a :*: Only b

-- PairOf a b f is isomorphic to (f a, f b)
getPair :: Pair a b f -> (f a, f b)
getPair (Only fa :*: Only fb) = (fa, fb)

mkPair :: (f a, f b) -> Pair a b f
mkPair (fa, fb) = Only fa :*: Only fb

unzip :: (Functor f, Rank2.Distributive g) => f (g Identity) -> g f
unzip = Rank2.cotraverse (fmap runIdentity)
