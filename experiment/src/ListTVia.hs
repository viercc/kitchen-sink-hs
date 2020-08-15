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

{- Made FMonad module out of it! -}
import FMonad

type    ListT :: (Type -> Type) -> (Type -> Type)
newtype ListT m a = ListT { runListT :: FreeT ((,) a) m () }

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
 = wrap . fjoin . fjoin . ffmap (ffmap pf) . ffmap pf . unwrap
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

