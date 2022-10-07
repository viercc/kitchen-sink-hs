{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}

module Monad.Efreet where

import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad.Trans.Free
import GHC.Generics ((:.:) (..))

-- | 'Efreet' is both 'Monad' and 'Comonad'.
data Efreet f x = x :> Maybe (f (Efreet f x))
  deriving (Functor)

-- | @Efreet f@ is isomorphic to @'Cofree' (Maybe :.: f)@
toCofree :: Functor f => Efreet f x -> Cofree (Maybe :.: f) x
toCofree (x :> mfr) = x :< fmap toCofree (Comp1 mfr)

fromCofree :: Functor f => Cofree (Maybe :.: f) x -> Efreet f x
fromCofree (x :< mfr) = x :> unComp1 (fmap fromCofree mfr)

-- | @Efreet f x@ is isomorphic to @'FreeT' f ((,) x) ()@
--
--   This can be compared to @ListT m x@ ("done right")
--
--   > newtype ListT m x = ListT { runListT :: m (Maybe (x, ListT m x)) }
--
--   Which also can be written in terms of FreeT:
--
--   > Efreet f   x ~ FreeT f       ((,) x) ()
--   > ListT    m x ~ FreeT ((,) x) m       ()
toFreeT :: Functor f => Efreet f x -> FreeT f ((,) x) ()
toFreeT = go
  where
    go (x :> mfr) = FreeT (x, goF mfr)

    goF Nothing = Pure ()
    goF (Just fr) = Free (fmap go fr)

fromFreeT :: Functor f => FreeT f ((,) x) () -> Efreet f x
fromFreeT = go
  where
    go (FreeT (x, mfr)) = x :> goF mfr

    goF (Pure ()) = Nothing
    goF (Free fr) = Just (fmap go fr)

glue :: Functor f => Efreet f b -> f (Efreet f b) -> Efreet f b
glue (x :> Nothing) fys = x :> Just fys
glue (x :> Just fxs) fys = x :> Just (fmap (`glue` fys) fxs)

instance Functor f => Applicative (Efreet f) where
  pure a = a :> Nothing

  (x :> Nothing) <*> y = x <$> y
  (x :> Just fxs) <*> y = glue (x <$> y) (fmap (<*> y) fxs)

instance Functor f => Monad (Efreet f) where
  (x :> Nothing) >>= k = k x
  (x :> Just fxs) >>= k = glue (k x) (fmap (>>= k) fxs)

instance Functor f => Comonad (Efreet f) where
  extract (x :> _) = x

  extend f ~xs@(_ :> mfr) = f xs :> fmap (fmap (extend f)) mfr

{-

Given various @f@, what Monad and Comonad @Efreet f@ is?

- @f = Const c@

  - @Efreet (Const c) x ~ (x, Maybe c)@
  - @Monad (Efreet (Const c))@ is @Writer (First c)@.

    - @First c@ is the one which wraps @Maybe c@, living in @Data.Monoid@.
      (There's also @Data.Semigroup.First@, unfortunately.)

  - @Comonad (Efreet (Const c))@ is @Env (Maybe c)@

- @f = Identity@

  - @Efreet Identity x ~ NonEmpty x@
  - @Monad@ and @Comonad@ instances, too, coincide to @NonEmpty@'s instance

- @f = (a, -)@

  - @Effect ((,) a) x@ is isomorphic to the list of elements of alternating types [x, a, x, a, ..., a, x].
    More concretely, the following Bifunctor:

    data AList a x = Single x | Cons x a (AList x a)

  - Comonad instance should not be surprising
  - Monad instance is given by the join operation like below

    [[x,a,x], a, [x], a, [x,a,x,a,x]] :: AList a (AList a x)
     |     |     | |     |         |
    [ x,a,x , a,  x , a,  x,a,x,a,x ] :: AList a x

-}
