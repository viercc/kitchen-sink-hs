{-# LANGUAGE
  QuantifiedConstraints,
  DerivingVia,
  DerivingStrategies,
  DeriveTraversable,
  StandaloneDeriving,
  
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

  FlipCompose(..),
  Day(..),
  ffirstDay, fsecondDay,
  intro1, elim1, assoc, disassoc,
  pureId, appendDay,
  
  FreeT'(..),

  -- * utilities
  inr, inl, eitherFreeT,
  firstFreeT, secondFreeT
) where

import Data.Kind

import Control.Applicative
import Control.Monad (join)
import Data.Bifunctor
import Data.Functor.Classes

import Data.Functor.Identity
import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State

import qualified Control.Monad.Free       as NonTrans
import           Control.Monad.Trans.Free

-- | Natural
type (~>) f g = forall x. f x -> g x

{-| Functor on 'Functor's

FFunctor laws:
>  ffmap id = id
>  ffmap f . ffmap g = ffmap (f . g)

-}

class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)

instance Functor f => FFunctor (Sum f) where
    ffmap _  (InL fa) = InL fa
    ffmap gh (InR ga) = InR (gh ga)

instance Functor f => FFunctor (Product f) where
    ffmap gh (Pair fa ga) = Pair fa (gh ga)

instance Functor f => FFunctor (Compose f) where
    ffmap gh = Compose . fmap gh . getCompose

instance FFunctor NonTrans.Free where
    ffmap gh = NonTrans.hoistFree gh

instance FFunctor IdentityT where
    ffmap fg = IdentityT . fg . runIdentityT

instance FFunctor (ReaderT e) where
    ffmap fg = ReaderT . fmap fg . runReaderT

instance FFunctor (WriterT m) where
    ffmap fg = WriterT . fg . runWriterT

instance FFunctor (StateT s) where
    ffmap fg = StateT . fmap fg . runStateT

{-
-- Ummmmmmm, (Functor f, Monad m) => Functor (FreeT f m)
-- So no, this is doomed to fail
instance Functor f => FFunctor (FreeT f) where
    ffmap = hoistFreeT_
-}

{-
-- This is not possible: @ContT r m@ uses @m@ in both covariant
-- and contravariant positions
instance FFunctor (ContT r) where
-}

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

instance FMonad NonTrans.Free where
    fpure = NonTrans.liftF
    fjoin = NonTrans.retract

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
    fpure = WriterT . fmap (\x -> (x, mempty))
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

-- | Flipped-order Compose.
--   
-- @FlipCompose f@ can be a 'FMonad' in the similar way 'Compose' is.
-- 
-- The only difference is @FlipCompose f@ composes @f@ to the right (_pre_compose)
-- compared to @Compose f@ which composes to the left (_post_compose).
type    FlipCompose :: (j -> k) -> (k -> Type) -> j -> Type
newtype FlipCompose f g a = FlipCompose { getFlipCompose :: g (f a) }

deriving stock instance (Functor g, Functor f) => Functor (FlipCompose f g)
deriving stock instance (Foldable g, Foldable f) => Foldable (FlipCompose f g)
deriving stock instance (Traversable g, Traversable f) => Traversable (FlipCompose f g)

deriving via (Compose (g :: Type -> Type) (f :: Type -> Type) a)
  instance (Show1 f, Show1 g, Show a) => Show (FlipCompose f g a)

deriving via (Compose (g :: Type -> Type) (f :: Type -> Type) a)
  instance (Read1 f, Read1 g, Read a) => Read (FlipCompose f g a)

deriving via (Compose (g :: Type -> Type) (f :: Type -> Type) a)
  instance (Eq1 f, Eq1 g, Eq a) => Eq (FlipCompose f g a)

deriving via (Compose (g :: Type -> Type) (f :: Type -> Type) a)
  instance (Ord1 f, Ord1 g, Ord a) => Ord (FlipCompose f g a)

deriving via (Compose (g :: Type -> Type) (f :: Type -> Type))
  instance (Applicative f, Applicative g) => Applicative (FlipCompose f g)

deriving via (Compose (g :: Type -> Type) (f :: Type -> Type))
  instance (Applicative f, Alternative g) => Alternative (FlipCompose f g)

instance Functor f => FFunctor (FlipCompose f) where
  ffmap gh = FlipCompose . gh . getFlipCompose

instance Monad f => FMonad (FlipCompose f) where
  fpure = FlipCompose . fmap return
  fjoin = FlipCompose . fmap join . getFlipCompose . getFlipCompose

-- | Day convolution. kan-extensions package have this, but
--   copying them here directly is easier to understand for
--   anyone unfamiliar with this type.
--
-- @Day@ can be thought as "what 'liftA2' takes as an argument".
-- 
-- > liftA2 :: forall a b x. (a -> b -> x) -> f a -> f b -> f x
-- > liftA2 :: forall x.     Day f f x                   -> f x
data Day f g x = forall a b. Day (a -> b -> x) (f a) (g b)

deriving instance Functor (Day f g)

-- 'Day' can be thought as a \"product type\" of Functors.
-- They can be mapped each component:
ffirstDay :: (f ~> f') -> (Day f g ~> Day f' g)
ffirstDay f' (Day ab_x fa gb) = Day ab_x (f' fa) gb

fsecondDay :: (g ~> g') -> (Day f g ~> Day f g')
fsecondDay g' (Day ab_x fa gb) = Day ab_x fa (g' gb)

-- Has 'Identity' as the unit:
intro1 :: f ~> Day Identity f
intro1 fa = Day (const id) (Identity ()) fa

elim1 :: Functor f => Day Identity f ~> f
elim1 (Day ab_x (Identity a) fb) = ab_x a <$> fb

-- Associative up to isomorphism:
assoc :: Day f (Day g h) ~> Day (Day f g) h
assoc (Day ay_x fa (Day bc_y gb hc))
  = let abc_x a b c = ay_x a (bc_y b c)
    in Day ($) (Day abc_x fa gb) hc

disassoc :: Day (Day f g) h ~> Day f (Day g h)
disassoc (Day yc_x (Day ab_y fa gb) hc)
  = let bca_x b c a = yc_x (ab_y a b) c
    in Day (\a k -> k a) fa (Day bca_x gb hc)

-- And @Applicative f@ can fold down product of @f@s
pureId :: Applicative f => Identity ~> f
pureId (Identity a) = pure a

appendDay :: Applicative f => Day f f ~> f
appendDay (Day ab_x fa fb) = liftA2 ab_x fa fb

instance FFunctor (Day f) where
    ffmap = fsecondDay

instance (Applicative f) => FMonad (Day f) where
    fpure :: g ~> Day f g
    fpure = ffirstDay pureId . intro1
    {-
       (ffirstDay pureId :: Day Identity g ~> Day f g) .
       (intro1           :: g ~> Day Identity g)
    -}

    fjoin :: Day f (Day f g) ~> Day f g
    fjoin = ffirstDay appendDay . assoc
    {-
       (ffirstDay appendDay :: Day (Day f f) g ~> Day f g) .
       (assoc               :: Day f (Day f g) ~> Day (Day f f) g)
    -}

{-----------------------------------------------------
 =
 =                  FreeT zone!
 =
------------------------------------------------------}

-- | FreeT' is argument-flipped 'FreeT'
newtype FreeT' m f b = FreeT' { unFreeT' :: FreeT f m b }
    deriving (Applicative, Monad) via (FreeT f m)

-- Sadly, Functor (FreeT m f) uses liftM instead of fmap,
-- meaning (Monad m, Functor f) => Functor (FreeT f m).
-- Maybe that was for backward compatibility,
-- but I want (Functor m, Functor f) => ...
fmapFreeT_ :: (Functor f, Functor m) => (a -> b) -> FreeT f m a -> FreeT f m b
fmapFreeT_ f = let go = FreeT . fmap (bimap f go) . runFreeT in go

ffmapFreeF :: forall f g a. (f ~> g) -> FreeF f a ~> FreeF g a
ffmapFreeF _  (Pure a)  = Pure a
ffmapFreeF fg (Free fb) = Free (fg fb)

-- Same!
transFreeT_, firstFreeT :: forall f g m. (Functor g, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
transFreeT_ fg =
  let go = FreeT . fmap (fmap go . ffmapFreeF fg) . runFreeT in go
firstFreeT = transFreeT_

-- And!
hoistFreeT_, secondFreeT :: forall f m n. (Functor f, Functor n) => (m ~> n) -> FreeT f m ~> FreeT f n
hoistFreeT_ fg = let go = FreeT . fmap (fmap go) . fg . runFreeT in go
secondFreeT = hoistFreeT_

instance (Functor m, Functor f) => Functor (FreeT' m f) where
    fmap f (FreeT' mx) = FreeT' (fmapFreeT_ f mx)

instance Functor m => FFunctor (FreeT' m) where
    ffmap f = FreeT' . transFreeT_ f . unFreeT'

inr :: Functor m => m ~> FreeT f m
inr = FreeT . fmap Pure

inl :: (Functor f, Monad m) => f ~> FreeT f m
inl = FreeT . return . Free . fmap return

eitherFreeT :: Monad n => (f ~> n) -> (m ~> n) -> (FreeT f m ~> n)
eitherFreeT nt1 nt2 = go
  where
    go ma =
      do v <- nt2 (runFreeT ma)
         case v of
           Pure a  -> return a
           Free fm -> nt1 fm >>= go

instance Monad m => FMonad (FreeT' m) where
    fpure :: forall g. Functor g => g ~> FreeT' m g
    fpure = FreeT' . inl
    
    fjoin :: forall g. Functor g => FreeT' m (FreeT' m g) ~> FreeT' m g
    fjoin = FreeT' . fjoin_ . transFreeT_ unFreeT' . unFreeT'
      where
        fjoin_ :: FreeT (FreeT g m) m ~> FreeT g m
        fjoin_ = eitherFreeT id inr
