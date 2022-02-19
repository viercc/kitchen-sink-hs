{-# LANGUAGE
  RankNTypes,
  QuantifiedConstraints,
  ExistentialQuantification,
  TypeOperators,
  PolyKinds,
  
  StandaloneKindSignatures
#-}
{- |

This is not possible: @'Control.Monad.Trans.Cont.ContT' r m@ uses @m@ in both covariant
and contravariant positions.
> instance FFunctor (ContT r) where

Ideally this instance should have existed, but a historical quirk prevent it to exist:
> instance Functor f => FFunctor (FreeT f)
Because, 'Control.Monad.Free.Trans.FreeT' defines its @Functor@ instance as
> instance (Functor f, Monad m)   => Functor (FreeT f m)
But beging @FFunctor (FreeT f)@ require it to be broader, more accurate constraint below.
> instance (Functor f, Functor m) => Functor (FreeT f m)
@Functor@ was not a superclass of @Monad@ back when @FreeT@ is made.

-}
module FFunctor(
  type (~>),
  FFunctor(..)
) where

import Data.Kind ( Type, Constraint )

import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose

import Data.Functor.Day
import Data.Functor.Day.Curried

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State
import Control.Applicative.Lift

import qualified Control.Monad.Free       as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch
import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal

-- | Natural
type (~>) f g = forall x. f x -> g x

{-| Endofunctors on the category of 'Functor's

FFunctor laws:
>  ffmap id = id
>  ffmap f . ffmap g = ffmap (f . g)

-}

type  FFunctor :: ((Type -> Type) -> (Type -> Type)) -> Constraint
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g x -> ff h x)

instance Functor f => FFunctor (Sum f) where
    ffmap _  (InL fa) = InL fa
    ffmap gh (InR ga) = InR (gh ga)

instance Functor f => FFunctor (Product f) where
    ffmap gh (Pair fa ga) = Pair fa (gh ga)

instance Functor f => FFunctor (Compose f) where
    ffmap gh = Compose . fmap gh . getCompose

instance FFunctor Lift where
    ffmap gh = mapLift gh

instance FFunctor FreeM.Free where
    ffmap = FreeM.hoistFree

instance FFunctor FreeMChurch.F where
    ffmap = FreeMChurch.hoistF

instance FFunctor FreeAp.Ap where
    ffmap = FreeAp.hoistAp

instance FFunctor FreeApFinal.Ap where
    ffmap = FreeApFinal.hoistAp

instance FFunctor IdentityT where
    ffmap fg = IdentityT . fg . runIdentityT

instance FFunctor (ReaderT e) where
    ffmap fg = ReaderT . fmap fg . runReaderT

instance FFunctor (WriterT m) where
    ffmap fg = WriterT . fg . runWriterT

instance FFunctor (StateT s) where
    ffmap fg = StateT . fmap fg . runStateT

instance FFunctor (Day f) where
    ffmap = trans2

instance Functor f => FFunctor (Curried f) where
    ffmap gh (Curried t) = Curried (gh . t)
