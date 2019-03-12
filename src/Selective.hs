{-

Selective Applicative Functors
https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf

-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Selective where

import Control.Applicative
import Control.Arrow

class Applicative f => Selective f where
  select :: f (Either a b) -> f (a -> b) -> f b
  select x y = either id (\(a,f) -> f a) <$> biselect (swapE <$> x) (Right <$> y)

  biselect :: f (Either a b) -> f (Either a c) -> f (Either a (b,c))
  biselect x y = select (fmap Left . swapE <$> x) ((\e a -> fmap (a,) e) <$> y)

  {-# MINIMAL select | biselect #-}

{-

Selective laws

-- Identity
x <*? pure id = either id id <$> x

-- Distributivity; note that y and z have the same type f (a -> b)
pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z)

-- Associativity

x :: f (Either a b)
y :: f (Either c (a -> b))
z :: f (c -> a -> b)
x <*? (y <*? z) = (f <$> x) <*? (g <$> y) <*? (h <$> z)
  where
    f :: Either a b -> Either a (Either (c,a) b)
    f x = Right <$> x

    g :: Either c (a -> b) -> (a -> Either (c,a) b)
    g y = \a -> bimap (,a) ($a) y

    h :: (c -> a -> b) -> ((c,a) -> b)
    h z = uncurry z

-- Associativity

x :: f (Either a b)
y :: f (Either c (a -> b))
z :: f (c -> a -> b)
x <*? (y <*? z) = (f <$> x) <*? (g <$> y) <*? (h <$> z)
  where
    f :: Either a b -> Either a (Either (c,a) b)
    f x = Right <$> x

    g :: Either c (a -> b) -> (a -> Either (c,a) b)
    g y = \a -> bimap (,a) ($a) y

    h :: (c -> a -> b) -> ((c,a) -> b)
    h z = uncurry z

-}

-- distr1 = distr2

distr1 :: (Selective f)
       => Either a r -> f (a -> b -> r) -> f (a -> b) -> f r
distr1 x y z = pure x <*? liftA2 (<*>) y z

distr2 :: (Selective f)
       => Either a r -> f (a -> b -> r) -> f (a -> b) -> f r
distr2 x y z =
  liftA2 (\y' z' -> either id id $ y' <*> z')
         (pure (fmap Left x) <*? fmap (fmap Right) y)
         (pure (fmap Left x) <*? fmap (fmap Right) z)

{-

-- select ==> biselect ==> select

either id (\(a,f) -> f a)
  <$> select (fmap Left . swapE <$> (swapE <$> x))
             ((\e a -> fmap (a,) e) <$> (Right <$> y))
 =

either id (\(a,f) -> f a)
  <$> select (fmap Left <$> x)
             (fmap (\f a -> Right (a,f)) <$> y)

=

select (fmap (either id (...)) . fmap Left <$> x)
       ((fmap . fmap) (either id (\(a,f) -> f a)) . fmap (\f a -> Right (a,f)) <$> y)

=

select (fmap id x)
       (fmap ( (\f a -> either id (\(a,f) -> f a) (Right (a,f))) ) y)

=

select x (fmap (\f a -> f a) y)

=

select x y

-- biselect ==> select ==> biselect

biselect x y
= select (fmap Left . swapE <$> x) ((\e a -> fmap (a,) e) <$> y)
= either id (\(a,f) -> f a)
    <$> biselect (swapE . fmap Left . swapE <$> x)
                 (Right . (\e a -> fmap (a,) e) <$> y)
= either id (\(a,f) -> f a)
    <$> biselect (first Left <$> x)
                 ((\e -> Right (\a -> fmap (a,) e)) <$> y)
  -- We stuck here!

-}

infixl 4 <*?
(<*?) :: (Selective f) => f (Either a b) -> f (a -> b) -> f b
(<*?) = select

branchS :: (Selective f) => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branchS x y z = (fmap Left <$> x) <*? (fmap Right <$> y) <*? z

branchS3 :: (Selective f)
         => f (Either a (Either b c))
         -> f (a -> d)
         -> f (b -> d)
         -> f (c -> d)
         -> f d
branchS3 x y z w =
      (fmap (fmap Left) <$> x)
  <*? (fmap (Right . Right) <$> y)
  <*? (fmap Right <$> z)
  <*? w

aponS :: (Selective f) => Prism s t a b -> f s -> f (a -> b) -> f t
aponS pr x y = select (swapE . view pr <$> x) (fmap (review pr) <$> y)

--------------------------------------------

{-
instance (Arrow arr) => Applicative (WrappedArrow arr e) where
  liftA2 f (WrapArrow x) (WrapArrow y) = WrapArrow $
    x &&& y >>> arr (uncurry f)
-}

instance (ArrowChoice arr) => Selective (WrappedArrow arr e) where
  select (WrapArrow x) (WrapArrow y) = WrapArrow $
    arr dup >>> second x >>>
    arr distr >>> left (uncurryA y) >>> arr (either id snd)

uncurryA :: (Arrow arr) => arr e (a -> b) -> arr (e,a) b
uncurryA x = first x >>> arr (uncurry ($))

dup :: a -> (a,a)
dup a = (a,a)

distr :: (e, Either a b) -> Either (e,a) (e,b)
distr (e, Left a) = Left (e,a)
distr (e, Right b) = Right (e,b)

{-

Selective laws

-- Identity
x <*? pure id = either id id <$> x

Proof.

WrapArrow x <*? pure id = WrapArrow $
  arr dup >>> second x >>> arr distr >>>
  left (uncurryA (arr (const id))) >>> arr untag

    arr distr >>> left (uncurryA (arr (const id))) >>> arr (either id snd)
     = arr $ distr >>> left (first (const id) >>> uncurry ($)) >>> either id snd
     = arr $ distr >>> left (\(a,b) -> const id a b) >>> either id snd
     = arr $ distr >>> left snd >>> either id snd
     = arr $ distr >>> either snd snd
     = arr $ snd >>> either id id
  
 = WrapArrow $ arr dup >>> second x >>> arr snd >>> arr (either id id)
 = WrapArrow $ arr dup >>> arr snd >>> x >>> arr (either id id)
 = WrapArrow $ x >>> arr (either id id)
 = either id id <$> WrapArrow x

-- Distributivity; note that y and z have the same type f (a -> b)
pure x <*? (y *> z) = (pure x <*? y) *> (pure x <*? z)

pure x <*? (y *> z) = _

-- Associativity

-}

--------------------------------------------

swapE :: Either a b -> Either b a
swapE = either Right Left

data Prism s t a b = Prism
  { view :: s -> Either t a
  , review :: b -> t
  }

_Left :: Prism (Either a c) (Either b c) a b
_Left = Prism (either Right (Left . Right)) Left

_Right :: Prism (Either c a) (Either c b) a b
_Right = Prism (either (Left . Left) Right) Right

infixr 2 +.
(+.) :: Prism s t x y -> Prism x y a b -> Prism s t a b
Prism view1 rev1 +. Prism view2 rev2 =
  let view' s = case view1 s of
        Left t -> Left t
        Right x -> case view2 x of
          Left y -> Left (rev1 y)
          Right a  -> Right a
      rev' b = rev1 (rev2 b)
  in Prism view' rev'
