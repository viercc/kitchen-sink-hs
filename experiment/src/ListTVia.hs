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
import Control.Monad.Trans.Free

import Control.Monad (ap)
import Data.Monoid (Ap(..))
import Data.Bifunctor

type    ListT :: (Type -> Type) -> (Type -> Type)
newtype ListT m a = ListT { runListT :: FreeT ((,) a) m () }

-- FreeT' is (Flip FreeT)
newtype FreeT' m f b = FreeT' { unFreeT' :: FreeT f m b }
    deriving (Applicative, Monad) via (FreeT f m)

-- Sadly, Functor (FreeT m f) uses liftM instead of fmap,
-- meaning (Monad m, Functor f) => Functor (FreeT f m).
-- Maybe that was for backward compatibility,
-- but I want (Functor m, Functor f) => ...
instance (Functor m, Functor f) => Functor (FreeT' m f) where
  fmap f (FreeT' mx) = FreeT' (fmapFree' f mx)

fmapFree' :: (Functor f, Functor m) => (a -> b) -> FreeT f m a -> FreeT f m b
fmapFree' f = let go = FreeT . fmap (bimap f go) . runFreeT in go

-- Natural
type (~>) f g = forall x. f x -> g x

-- functor on @Functor@s
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)

-- monad on @Functor@s
class FFunctor ff => FMonad ff where
    fpure :: (Functor g) => g ~> ff g
    fjoin :: (Functor g) => ff (ff g) ~> ff g



{-

FFunctor laws:
   ffmap id = id
   ffmap f . ffmap g = ffmap (f . g)

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

instance Functor m => FFunctor (FreeT' m) where
    ffmap f = FreeT' . hoistF f . unFreeT'

-- Same function from "free" uses (Monad m) => ...
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
        join_ = FMonadList . fjoin . ffmap (plug . first runFMonadList) . runFMonadList
        plug :: forall f x. Functor f => (f (), x) -> f x
        plug (f_,a) = a <$ f_

{-

Is it really lawful?

(I'll skip `FreeT' m` being lawful `FMonad` part)

Preparation:

I'll use the following aliases:
  wrap = FMonadList
  unwrap = runFMonadList
  pf = plug . first unwrap

Using these aliases:
  return = wrap . fpure . (, ())
  join_  = wrap . fjoin . ffmap pf . unwrap

Also, for any natural transformation `n :: f ~> g`,
  Lemma [plugnat]
  plug . first n :: (f (), b) -> g b
   = \(f_, b) -> b <$ n f_
     -- (b <$) = fmap (const b), and fmap commutes with n
   = \(f_, b) -> n (b <$ f_)
   = n . plug

Note that they are all natural transformations:
* ffmap _
* fpure
* fjoin

(1) Left unit:

join_ . return
 = wrap . fjoin . ffmap pf . unwrap . wrap . fpure . (, ())
 = wrap . fjoin . ffmap pf . fpure . (, ())
   -- naturality of fpure
 = wrap . fjoin . fpure . pf . (, ())
                          ^^^^^^^^^^^
   {
     pf . (, ())
      = plug . first unwrap . (, ())
      = (() <$) . unwrap
      = fmap (const () :: () -> ()) . unwrap
      = fmap id . unwrap
      = unwrap
   }
 = wrap . fjoin . fpure . unwrap
   -- FMonad law
 = wrap . id . unwrap
 = id

(2) Right unit:

join_ . fmap return
 = wrap . fjoin . ffmap pf . unwrap .
   wrap . ffmap (first return) . unwrap
 = wrap . fjoin . ffmap pf . ffmap (first return) . unwrap
   -- FFunctor law
 = wrap . fjoin . ffmap (pf . first return) . unwrap
                         ^^^^^^^^^^^^^^^^^
   {
     pf . first return
      = plug . first unwrap . first (wrap . fpure . (,()))
      = plug . first (fpure . (,()))
      = plug . first fpure . first (,())
        -- [plugnat]
      = fpure . plug . first (,())
      = fpure . plug . (\(a,b) -> ((a,()), b))
      = fpure . (\(a,b) -> b <$ (a, ()))
      = fpure . (\(a,b) -> (a,b))
      = fpure
   }
 = wrap . fjoin . ffmap fpure . unwrap
   -- FMonad law
 = wrap . id . unwrap
 = id

(3) Associativity:

join_ . join_
 = wrap . fjoin . ffmap pf . unwrap .
   wrap . fjoin . ffmap pf . unwrap
 = wrap . fjoin . ffmap pf . fjoin . ffmap pf . unwrap
   -- naturality of fjoin
 = wrap . fjoin . fjoin . ffmap (ffmap pf) . ffmap plug . unwrap
 = wrap . fjoin . fjoin . ffmap (ffmap pf . pf) . unwrap

join_ . fmap join_
 = wrap . fjoin . ffmap pf . unwrap .
   wrap . ffmap (first (wrap . fjoin . ffmap pf . unwrap)) . unwrap
 = wrap . fjoin . ffmap pf .
          ffmap (first (wrap . fjoin . ffmap pf . unwrap)) . unwrap
 = wrap . fjoin .
     ffmap (pf . first (wrap . fjoin . ffmap pf . unwrap)) . unwrap
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   {
     pf . first (wrap . fjoin . ffmap pf . unwrap) 
      = plug . first unwrap . first (wrap . fjoin . ffmap pf . unwrap)
      = plug . first (fjoin . ffmap pf . unwrap)
      = plug . first (fjoin . ffmap pf) . first unwrap
        -- [plugnat]
      = fjoin . ffmap pf . plug . first unwrap
      = fjoin . ffmap pf . pf
   }
 = wrap . fjoin . ffmap (fjoin . ffmap pf . pf) . unwrap
 = wrap . fjoin . ffmap fjoin . ffmap (ffmap pf . f) . unwrap
   -- FMonad law
 = wrap . fjoin . fjoin . ffmap (ffmap pf . pf) . unwrap
 = join_ . join_

-}

deriving via (FMonadList (FreeT' m))
  instance Functor m => Functor (ListT m)

deriving via (FMonadList (FreeT' m))
  instance Monad m => Applicative (ListT m)

deriving via (FMonadList (FreeT' m))
  instance Monad m => Monad (ListT m)

-- deriving Monoid is easy!
deriving via (Ap (FreeT ((,) a) m) ())
  instance Monad m => Semigroup (ListT m a)

deriving via (Ap (FreeT ((,) a) m) ())
  instance Monad m => Monoid (ListT m a)

-- MonadTrans is specific to ListT
instance MonadTrans ListT where
  lift ma = ListT . FreeT $ ma >>= \a -> return $ Free (a, return ())

-- For test:
collapse :: Monad m => ListT m () -> m ()
collapse = iterT (\((), m) -> m) . runListT

eval :: Show a => ListT IO a -> IO ()
eval ma = collapse (ma >>= (lift . pr))
  where pr a = putStrLn $ "ValueProduced[" ++ show a ++ "]"

test1, test2, test3 :: ListT IO Int
test1 = lift (print "A") >> mempty
test2 = lift (print "B") >> pure 1
test3 = lift (print "C") >> (pure 2 <> pure 3)

