{-# LANGUAGE
  StandaloneKindSignatures,
  DerivingVia,
  DerivingStrategies,
  DeriveFunctor,
  StandaloneDeriving,
  RankNTypes,
  ScopedTypeVariables,
  InstanceSigs,
  TypeOperators,
  TupleSections,
  QuantifiedConstraints
#-}
module ListTVia where

import Data.Kind
import Control.Monad.Trans
import Control.Monad.Writer (WriterT(..))
import Control.Monad.Trans.Free

import Control.Monad (ap)
import Data.Monoid (Ap(..))
import Data.Bifunctor

type    ListT :: (Type -> Type) -> (Type -> Type)
newtype ListT m a = ListT { runListT :: FreeT ((,) a) m () }

-- FreeT' is (Flip FreeT)
newtype FreeT' m f b = FreeT' { unFreeT' :: FreeT f m b }
    deriving (Applicative, Monad) via (FreeT f m)

instance (Functor m, Functor f) => Functor (FreeT' m f) where
  fmap f (FreeT' mx) = FreeT' (go mx)
    where go = FreeT . fmap (bimap f go) . runFreeT

-- Natural
type (~>) f g = forall x. f x -> g x

class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)

class FFunctor ff => FMonad ff where
    fpure :: (Functor g) => g ~> ff g
    fjoin :: (Functor g) => ff (ff g) ~> ff g

instance Functor m => FFunctor (FreeT' m) where
    ffmap f = FreeT' . hoistF f . unFreeT'

hoistF :: forall f g m. (Functor f, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
hoistF fg =
  let fg' :: forall a. FreeF f a ~> FreeF g a
      fg' (Pure a) = Pure a
      fg' (Free fr) = Free (fg fr)

      go :: FreeT f m ~> FreeT g m
      go (FreeT mfx) = FreeT $ fmap (fg' . fmap go) mfx
  in go

instance Monad m => FMonad (FreeT' m) where
    fpure :: Functor g => g ~> FreeT' m g
    fpure gx = FreeT' (liftF gx)

    fjoin :: Functor g => FreeT' m (FreeT' m g) ~> FreeT' m g
    fjoin =  FreeT' . fjoin_ . transFreeT unFreeT' . unFreeT'

fjoin_ :: (Monad m, Functor g) => FreeT (FreeT g m) m ~> FreeT g m
fjoin_ = retractT

newtype FMonadList mm a = FMonadList { runFMonadList :: mm ((,) a) () }

instance (FFunctor mm) => Functor (FMonadList mm) where
    fmap f = FMonadList . ffmap (first f) . runFMonadList
      -- f :: a -> b
      -- first f :: forall c. (a, c) -> (b, c)

instance (FMonad mm) => Applicative (FMonadList mm) where
    pure = return
    (<*>) = ap

instance (FMonad mm) => Monad (FMonadList mm) where
    return a = FMonadList $ fpure (a, ())
    ma >>= k = join_ (fmap k ma)
      where
        join_ = FMonadList . fjoin . ffmap plug . runFMonadList
        plug :: forall a x. (FMonadList mm a, x) -> mm ((,) a) x
        plug (m,x) = x <$ runFMonadList m

deriving via (FMonadList (FreeT' m))
  instance Functor m => Functor (ListT m)

deriving via (FMonadList (FreeT' m))
  instance Monad m => Applicative (ListT m)

deriving via (FMonadList (FreeT' m))
  instance Monad m => Monad (ListT m)

deriving via (Ap (FreeT ((,) a) m) ())
  instance Monad m => Semigroup (ListT m a)

deriving via (Ap (FreeT ((,) a) m) ())
  instance Monad m => Monoid (ListT m a)



instance MonadTrans ListT where
  lift ma = ListT . FreeT $ ma >>= \a -> return $ Free (a, return ())

collect :: Monad m => ListT m a -> m [a]
collect = fmap snd . runWriterT . foldFreeT step . runListT
  where step (a,r) = WriterT $ return (r, [a])

test1, test2, test3 :: ListT IO Int
test1 = lift (print "A") >> mempty
test2 = lift (print "B") >> pure 1
test3 = lift (print "C") >> (pure 2 <> pure 3)
