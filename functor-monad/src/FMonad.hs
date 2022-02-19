{-# LANGUAGE
  QuantifiedConstraints,
  
  StandaloneKindSignatures,
  PolyKinds,
  
  RankNTypes,
  ExistentialQuantification,
  ScopedTypeVariables,
  TypeApplications,
  
  InstanceSigs,
  TypeOperators,
  TupleSections
#-}
module FMonad(
  type (~>),
  FFunctor(..),
  FMonad(..),
) where

import Control.Monad (join)
import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State

import Control.Applicative.Lift

import qualified Control.Monad.Free       as FreeM
import qualified Control.Monad.Free.Church as FreeMChurch
import qualified Control.Applicative.Free as FreeAp
import qualified Control.Applicative.Free.Final as FreeApFinal

import Data.Functor.Day

import FFunctor

{-| Monad on 'Functor's

FMonad laws:

[fpure is natural in g]

    ∀(n :: g ~> h). ffmap n . fpure = fpure . n

[fjoin is natural in g]

    ∀(n :: g ~> h). ffmap n . fjoin = fjoin . ffmap (ffmap n)

[Left unit]

    fjoin . fpure = id

[Right unit]

    fjoin . fmap fpure = id

[Associativity]

    fjoin . fjoin = fjoin . ffmap fjoin

-}
class FFunctor ff => FMonad ff where
    fpure :: (Functor g) => g ~> ff g
    fjoin :: (Functor g) => ff (ff g) ~> ff g


instance Functor f => FMonad (Sum f) where
    fpure = InR
    fjoin (InL fa) = InL fa
    fjoin (InR (InL fa)) = InL fa
    fjoin (InR (InR ga)) = InR ga

instance (Functor f, forall a. Monoid (f a)) => FMonad (Product f) where
    fpure = Pair mempty
    fjoin (Pair fa1 (Pair fa2 ga)) = Pair (fa1 <> fa2) ga

instance Monad f => FMonad (Compose f) where
    fpure = Compose . return
    fjoin = Compose . join . fmap getCompose . getCompose

instance FMonad Lift where
    fpure = Other
    fjoin (Pure a) = Pure a
    fjoin (Other (Pure a)) = Pure a
    fjoin (Other (Other fa)) = Other fa

instance FMonad FreeM.Free where
    fpure = FreeM.liftF
    fjoin = FreeM.retract

instance FMonad FreeMChurch.F where
    fpure = FreeMChurch.liftF
    fjoin = FreeMChurch.retract

instance FMonad FreeAp.Ap where
    fpure = FreeAp.liftAp
    fjoin = FreeAp.retractAp

instance FMonad FreeApFinal.Ap where
    fpure = FreeApFinal.liftAp
    fjoin = FreeApFinal.retractAp

instance FMonad IdentityT where
    fpure = IdentityT
    fjoin (IdentityT (IdentityT fa)) = IdentityT fa

instance FMonad (ReaderT e) where
    -- See the similarity between 'Compose' @((->) e)@
    
    -- return :: x -> (e -> x)
    fpure = ReaderT . return
    -- join :: (e -> e -> x) -> (e -> x)
    fjoin = ReaderT . join . fmap runReaderT . runReaderT

instance Monoid m => FMonad (WriterT m) where
    -- See the similarity between 'FlipCompose' @(Writer m)@

    -- fmap return :: f x -> f (Writer m x)
    fpure = WriterT . fmap (, mempty)
    -- fmap join :: f (Writer m (Writer m x)) -> f (Writer m x)
    fjoin = WriterT . fmap (\((x,m1),m2) -> (x, m2<>m1)) . runWriterT . runWriterT

{-

If everything is unwrapped, FMonad @(StateT s)@ is

  fpure :: forall f. Functor f => f x -> s -> f (x, s)
  fjoin :: forall f. Functor f => (s -> s -> f ((x, s), s)) -> s -> f (x, s)

And if this type was generic in @s@ without any constraint like @Monoid s@,
the only possible implementations are

  -- fpure is uniquely:
  fpure fx s = (,s) <$> fx

  -- fjoin is one of the following three candidates
  fjoin1 stst s = (\((x,_),_) -> (x,s)) <$> stst s s
  fjoin2 stst s = (\((x,_),s) -> (x,s)) <$> stst s s
  fjoin3 stst s = (\((x,s),_) -> (x,s)) <$> stst s s

But none of them satisfy the FMonad law.

  (fjoin1 . fpure) st
    = fjoin1 $ \s1 s2 -> (,s1) <$> st s2
    = \s -> (\((x,_),_) -> (x,s)) <$> ((,s) <$> st s)
    = \s -> (\(x,_) -> (x,s)) <$> st s
    /= st
  (fjoin2 . fpure) st
    = fjoin2 $ \s1 s2 -> (,s1) <$> st s2
    = \s -> (\((x,_),s') -> (x,s')) <$> ((,s) <$> st s)
    = \s -> (\(x,_) -> (x,s)) <$> st s
    /= st
  (fjoin3 . ffmap fpure) st
    = fjoin2 $ \s1 s2 -> fmap (fmap (,s2)) . st s1
    = \s -> ((\((x,s'),_) -> (x,s')) . fmap (,s)) <$> st s
    = \s -> (\(x,_) -> (x,s)) <$> st s
    /= st

So the lawful @FMonad (StateT s)@ will utilize some structure
on @s@.

One way would be seeing StateT as the composision of Reader s and
Writer s:

  StateT s m ~ Reader s ∘ m ∘ Writer s 
    where (∘) = Compose

By this way

  StateT s (StateT s m) ~ Reader s ∘ Reader s ∘ m ∘ Writer s ∘ Writer s 

And you can collapse the nesting by applying @join@ for @Reader s ∘ Reader s@
and @Writer s ∘ Writer s@. To do so, it will need @Monoid s@ for @Monad (Writer s)@.

-}

instance Monoid s => FMonad (StateT s) where
  -- Note that this is different to @lift@ in 'MonadTrans',
  -- whilst having similar type and actually equal in
  -- several other 'FMonad' instances.
  -- 
  -- See the discussion below.
  fpure fa = StateT $ \_ -> (,mempty) <$> fa
  
  fjoin = StateT . fjoin_ . fmap runStateT . runStateT
    where
      fjoin_ :: forall f a. (Functor f) => (s -> s -> f ((a, s), s)) -> s -> f (a, s)
      fjoin_ = fmap (fmap joinWriter) . joinReader
        where
          joinReader :: forall x. (s -> s -> x) -> s -> x
          joinReader = join

          joinWriter :: forall x. ((x,s),s) -> (x,s)
          joinWriter ((a,s1),s2) = (a, s2 <> s1)

{-

Note [About FMonad (StateT s) instance]

@fpure@ has a similar (Functor instead of Monad) type signature
with 'lift', but due to the different laws expected on them,
they aren't necessarily same.

@lift@ for @StateT s@ must be, by the 'MonadTrans' laws,
the one currently used. And this is not because the parameter @s@
is generic, so it applies if we have @Monoid s =>@ constraints like
the above instance.

One way to have @lift = fpure@ here is requiring @s@ to be a type with
group operations, @Monoid@ + @inv@ for inverse operator,
instead of just being a monoid.

> fpure fa = StateT $ \s -> (,s) <$> fa 
> fjoin = StateT . fjoin_ . fmap runStateT . runStateT
>   where fjoin_ mma s = fmap (fmap (joinGroup s)) $ joinReader mma s
>         joinReader = join
>         joinGroup s ((x,s1),s2) = (x, s2 <> inv s <> s1)

-}

instance (Applicative f) => FMonad (Day f) where
    fpure :: g ~> Day f g
    fpure = day (pure id)
    {-
       day :: f (a -> b) -> g a -> Day f g b
    -}

    fjoin :: Day f (Day f g) ~> Day f g
    fjoin = trans1 dap . assoc
    {-
       dap :: Day f f ~> f
       trans1 dap :: Day (Day f f) g ~> Day f g
       assoc               :: Day f (Day f g) ~> Day (Day f f) g
    -}
