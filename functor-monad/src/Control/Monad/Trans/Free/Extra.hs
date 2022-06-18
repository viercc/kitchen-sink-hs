{-# LANGUAGE
  RankNTypes,
  ScopedTypeVariables,
  TypeOperators
#-}
module Control.Monad.Trans.Free.Extra where

import Data.Bifunctor
import Control.Monad.Trans.Free

import FFunctor (type (~>))
import Control.Arrow ((>>>))

-- Sadly, Functor (FreeT m f) uses liftM instead of fmap,
-- meaning (Monad m, Functor f) => Functor (FreeT f m).
-- Maybe that was for backward compatibility,
-- but I want (Functor m, Functor f) => ...
fmapFreeT_ :: (Functor f, Functor m) => (a -> b) -> FreeT f m a -> FreeT f m b
fmapFreeT_ f = let go = FreeT . fmap (bimap f go) . runFreeT in go

ffmapFreeF :: forall f g a. (f ~> g) -> FreeF f a ~> FreeF g a
ffmapFreeF _  (Pure a)  = Pure a
ffmapFreeF fg (Free fb) = Free (fg fb)

transFreeT_ :: forall f g m. (Functor g, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
transFreeT_ fg =
  let go = FreeT . fmap (fmap go . ffmapFreeF fg) . runFreeT in go

traverseFreeT_ :: (Traversable f, Traversable m, Applicative g)
  => (a -> g b) -> FreeT f m a -> g (FreeT f m b)
traverseFreeT_ f = go
  where
    go (FreeT x) = FreeT <$> traverse goF x
    goF (Pure a)   = Pure <$> f a
    goF (Free fmx) = Free <$> traverse go fmx

inr :: Functor m => m ~> FreeT f m
inr = FreeT . fmap Pure

inl :: (Functor f, Monad m) => f ~> FreeT f m
inl = FreeT . return . Free . fmap return

eitherFreeT_ :: Monad n => (f ~> n) -> (m ~> n) -> (FreeT f m ~> n)
eitherFreeT_ nt1 nt2 = go
  where
    go ma =
      do v <- nt2 (runFreeT ma)
         case v of
           Pure a  -> return a
           Free fm -> nt1 fm >>= go

fconcatFreeT_ :: forall f m. (Functor f, Functor m) => FreeT f (FreeT f m) ~> FreeT f m
fconcatFreeT_ = outer
  where
    -- type T = FreeT f
    -- type F = FreeF f
    --
    --
    -- runFreeT :: T m x -> m (F x (T m x)) 
    
    outer :: forall a. FreeT f (FreeT f m) a -> FreeT f m a
    outer =                             -- T (T m) a
        runFreeT >>>                    -- T m (F a (T (T m) a))
        fmapFreeT_ (fmap outer) >>>     -- T m (F a (T m a))
        inner                           -- T m a
    
    inner :: forall a. FreeT f m (FreeF f a (FreeT f m a)) -> FreeT f m a
    inner =           -- T m (F a (T m a))
        runFreeT >>>  -- m (F (F a (T m a)) (T m (F a (T m a))))
        fmap step >>> -- m (F a (T m a))
        FreeT

    -- F a b = a + f b
    --
    -- step :: a + f (T m a) + f (T m (a + f (T m a))) -> a + f (T m a)
    --                            ^^^^^^^^^^^^^^^^^^^ input of inner
    step :: forall a. FreeF f (FreeF f a (FreeT f m a)) (FreeT f m (FreeF f a (FreeT f m a))) -> FreeF f a (FreeT f m a)
    step (Pure (Pure a)) = Pure a
    step (Pure (Free ft)) = Free ft
    step (Free fRec) = Free (fmap inner fRec)