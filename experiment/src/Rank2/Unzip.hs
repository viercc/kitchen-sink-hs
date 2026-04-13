{-# LANGUAGE TypeOperators #-}
module Rank2.Unzip where

import qualified Rank2
import Rank2 (Only(..))
import GHC.Generics
import Data.Functor.Identity

-- Generalized unzip
unzipG :: (Functor f, Rank2.Distributive g) => f (g Identity) -> g f
unzipG = Rank2.cotraverse (fmap runIdentity)

unzip2 :: Functor f => f (a, b) -> (f a, f b)
unzip2 = unPair . unzipG . fmap mkPair

unzip3 :: Functor f => f (a,b,c) -> (f a, f b, f c)
unzip3 = unTup3 . unzipG . fmap mkTup3

type Pair a b = Only a :*: Only b

mkPair :: (a, b) -> Pair a b Identity
mkPair (a,b) = Only (Identity a) :*: Only (Identity b)

unPair :: Pair a b f -> (f a, f b)
unPair (Only fa :*: Only fb) = (fa, fb)

type Tup3 a b c = Only a :*: Only b :*: Only c

mkTup3 :: (a, b, c) -> Tup3 a b c Identity
mkTup3 (a, b, c) = Only (Identity a) :*: Only (Identity b) :*: Only (Identity c)

unTup3 :: Tup3 a b c f -> (f a, f b, f c)
unTup3 (Only fa :*: Only fb :*: Only fc) = (fa, fb, fc)
