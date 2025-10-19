{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- | Category of "partial functions" @a -> Maybe b@
module Partial where

import Prelude hiding (id, (.))
import Control.Category ( Category(..) )
import Control.Arrow ( Arrow(..), ArrowChoice, Kleisli(..) )

import Witherable (Filterable(..))
import Data.These (These(..))
import Data.These.Combinators qualified as These

-- * Type

newtype Partial a b = Partial {
    runPartial :: a -> Maybe b
  }
  deriving (Category, Arrow, ArrowChoice) via (Kleisli Maybe)

type (-?) = Partial
infixr 1 -?

-- | (Usual) functions are morphisms of category Hask
type Hask = (->)

-- * Special morphisms

-- | zero morphism
--
-- 'Void' is the zero object of 'Partial' category.
-- 
-- * @zero :: a -? Void@ is unique for any @a@
-- * @zero :: Void -? b@ is unique for any @b@
zero :: a -? b
zero = Partial (const Nothing)

depoint :: Maybe a -? a
depoint = Partial id

-- * Product, coproduct, tensor product

-- ** These is the product

pfst :: These a b -? a
pfst = Partial These.justHere

psnd :: These a b -? b
psnd = Partial These.justThere

ppair :: (x -? a) -> (x -? b) -> (x -? These a b)
ppair (Partial f) (Partial g) = Partial $ \x ->
  case (f x, g x) of
    (Nothing, Nothing) -> Nothing
    (Just a,  Nothing) -> Just $ This a
    (Nothing, Just b)  -> Just $ That b
    (Just a,  Just b)  -> Just $ These a b

bipmapThese :: (a -? a') -> (b -? b') -> (These a b -? These a' b')
bipmapThese f g = ppair (f . pfst) (g . psnd)

-- ** Either is the coproduct
pleft :: a -? Either a b
pleft = arr Left

pright :: b -? Either a b
pright = arr Right

peither :: (a -? y) -> (b -? y) -> (Either a b -? y)
peither (Partial f) (Partial g) = Partial $ either f g

bipmapEither :: (a -? a') -> (b -? b') -> (Either a b -? Either a' b')
bipmapEither f g = peither (pleft . f) (pright . g)

-- ** Tuple is a tensor product (sometimes named "the smash product")

bipmapTuple :: (a -? a') -> (b -? b') -> ((a,b) -? (a',b'))
bipmapTuple (Partial f) (Partial g) = Partial $ \ (a,b) -> (,) <$> f a <*> g b

-- * Functors from Partial to Hask

-- | @'Maybe'@ is a functor from Partial to Hask
bind :: (a -? b) -> Hask (Maybe a) (Maybe b)
bind f ma = ma >>= runPartial f

-- | Any @'Filterable' f@ is a functor from Partial to Hask
mapMaybe' :: Filterable f => (a -? b) -> Hask (f a) (f b)
mapMaybe' = mapMaybe . runPartial
