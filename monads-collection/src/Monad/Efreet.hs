{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Monad.Efreet where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree
import Control.Monad (ap)
import Control.Monad.Trans.Free
import Data.Bool (bool)
import GHC.Generics ((:.:) (..))
import MonadLaws

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

-- Efreet ((->) a) is strange! Let's investigate the smallest non-degenerate case : a = Bool!

data Tree x = Leaf x | Branch x (Tree x) (Tree x)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

toTree :: Efreet ((->) Bool) x -> Tree x
toTree (x :> Nothing) = Leaf x
toTree (x :> Just children) = Branch x (toTree (children False)) (toTree (children True))

fromTree :: Tree x -> Efreet ((->) Bool) x
fromTree (Leaf x) = x :> Nothing
fromTree (Branch x l r) = x :> Just (bool (fromTree l) (fromTree r))

instance Applicative Tree where
  pure = Leaf
  (<*>) = ap

instance Monad Tree where
  Leaf x >>= f = f x
  Branch x l r >>= f = glueTree (f x) (l >>= f, r >>= f)

glueTree :: Tree x -> (Tree x, Tree x) -> Tree x
glueTree (Leaf x) (yl, yr) = Branch x yl yr
glueTree (Branch x l r) ylr = Branch x (glueTree l ylr) (glueTree r ylr)

enumTree :: Enum1 Tree
enumTree ma = t1 <|> t2
  where
    t1 = Leaf <$> ma
    t2 = Branch <$> ma <*> t1 <*> t1
