{-# LANGUAGE RankNTypes #-}
module Monad.FTransducer where

import           Control.Monad
import           Monad.Free

type Transducer f g = forall r. (g r -> r) -> f r -> r

type Transducer' f g = forall x. f x -> Free g x

intoMonad :: (Functor f, Monad g) => Transducer f g -> f x -> g x
intoMonad trans fx = trans join (fmap return fx)

{-
to :: (Functor f, Functor g) => Transducer f g -> Transducer' f g
to = intoMonad
-}
to :: (Functor f) => Transducer f g -> Transducer' f g
to trans = trans Free . fmap Pure

cataFree :: (Functor f) => (x -> r) -> (f r -> r) -> Free f x -> r
cataFree ret step = go
  where go (Pure x)   = ret x
        go (Free fmx) = step (fmap go fmx)

from :: (Functor g) => Transducer' f g -> Transducer f g
from trans' step = cataFree id step . trans'

{-

from . to
  = \tr -> from (to tr)
  = \tr -> from (tr Free . fmap Pure)
  = \tr -> \step -> cataFree id step . tr Free . fmap Pure
  = \tr -> \step -> 

to . from
      -- eta
  = \tr' -> to (from tr')
      -- Definition of @from@
  = \tr' -> to (\step -> cataFree id step . tr')
      -- Definition of @to@
  = \tr' -> (\step -> cataFree id step . tr') Free . fmap Pure
      -- beta
  = \tr' -> cataFree id Free . tr' . fmap Pure
      -- naturality of @tr'@ (commutes with fmap)
  = \tr' -> cataFree id Free . fmap Pure . tr'
      -- fusion cata and fmap
  = \tr' -> cataFree Pure Free . tr'
      -- cataFree Pure Free = id
  = \tr' -> tr'
  = id
-}

{- Transducer is @Category@ -}
idTransducer :: Transducer f f
idTransducer = id

composeTransducer :: Transducer f g -> Transducer g h -> Transducer f h
composeTransducer = (.)

idTransducer' :: (Functor f) => Transducer' f f
idTransducer' = liftFree

composeTransducer' ::
  (Functor h) => Transducer' f g -> Transducer' g h -> Transducer' f h
composeTransducer' fg gh = foldFree gh . fg
