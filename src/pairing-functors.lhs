During play around objective package, I noticed following type has interesting property.

> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
> {-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
> {-# LANGUAGE UndecidableInstances #-}
> 
> import Control.Monad
> import Control.Comonad -- require comonad package
> 
> data N f r = N { unN :: forall x. f x -> (x, r) }

It is a Functor.

> instance Functor (N f) where
>    fmap f (N nat) = N $ fmap (fmap f) nat
>          -- or,   = N $ \fx -> let { (x,a) = nat fx } in (x, f a)

After few hours of google/hoogle, I gave up finding any existing module that includes this type. What is this type? If it is well known, what is the name? Is this useful or ignored because useless?

This is not my 100% original creation, because N was derived from Object found in objective package.

> data Object f g = Object {
>     runObject :: forall x. f x -> g (x, Object f g)
>   }

N f is a Functor which yields Object f Identity when Fix is applied to.

Following is a fact about this type and why I thought it is interesting.

N converts Reader to Writer, vice versa.
(Here I used (=) symbol for isomorphism between types)

N ((->) e) r
 = forall x. (e -> x) -> (x, r)
 = (e, r)

N ((,) d) r
 = forall x. (d, x) -> (x, r)
 = d -> r

N converts Store comonad to State monad, but inverse is not true.

> data Store s a = Store s (s -> a)
> type State s a = s -> (s, a)

N (Store s) r
 = forall x. (s, (s -> x)) -> (x, r)
 = forall x. s -> (s -> x) -> (x, r)
 = s -> (s, r)
 = State s r

N (State s) r
 = forall x. (s -> (s, x)) -> (x, r)
 = forall x. (s -> s, s -> x) -> (x, r)
 = forall x. (s -> s) -> (s -> x) -> (x, r)
 = (s -> s) -> (s, r)  -- ???

N can't take Maybe.

N Maybe r
 = forall x. Maybe x -> (x, r)
 = forall x. (() -> (x, r), x -> (x, r))
 = Void     -- because (() -> (x, r)) can't be implemented
Following function may be fun. I couldn't do it's inverse.

> data Cofree f a = Cofree a (f (Cofree f a))
> data Free f a = Pure a | Wrap (f (Free f a))

> unfree :: Free (N f) r -> N (Cofree f) r
> unfree (Pure r) = N $ \(Cofree a _) -> (a, r)
> unfree (Wrap n_f) = N $
>   \(Cofree _ f) -> let (cofree', free') = unN n_f f
>                    in unN (unfree free') cofree'

-----------------------------------------------------


WHEN f IS Comonad, (N f) IS Monad!!

> instance Comonad f => Applicative (N f) where
>   pure = return
>   (<*>) = ap
>   
> instance Comonad f => Monad (N f) where
>   return a = N $ \fx -> (extract fx, a)
>   nf >>= k = N $
>       \fx -> let (fx', a) = unN nf $ duplicate fx
>              in unN (k a) fx'

-----------------------------------------------------

> data Sum f g x = InL (f x) | InR (g x)
> data Prod f g x = Prod (f x) (g x)

N (Sum f g) r
 = forall x. (f x :+: g x) -> (x, r)
 = forall x. ((f x -> (x, r)), (g x -> (x, r))
 = (N f r, N g r)
 = Prod (N f) (N g) r

> data MealyF a b r = MealyF (a -> (b, r))
> data MooreF a b r = MooreF a (b -> r)

N (MooreF a b) r
 = forall x. (a, b -> x) -> (x, r)
 = forall x. a -> (b -> x) -> (x, r)
 = a -> (b, r)
 = MealyF a b r

N (MealyF a b) r
 = forall x. (a -> (b, x)) -> (x, r)
 = forall x. (a -> b, a -> x) -> (x, r)
 = forall x. (a -> b) -> (a -> x) -> (x, r)
 = (a -> b) -> (a, r)

> data Teletype x where
>   PutC :: Char -> Teletype ()
>   GetC :: Teletype Char

N Teletype r
 = forall x. Teletype x -> (x, r)
 = (Char -> ((), r), (Char, r))
 = (Char -> r, (Char, r))

You can implement N f (N g r) -> N (f `Compose` g) r,
but inverse is not possible, I think.

> data Compose f g x = Compose { unCompose :: f (g x) }
> press :: N f (N g r) -> N (f `Compose` g) r
> press n_fg = N $
>   \fg -> let (g, n_g) = unN n_fg $ unCompose fg
>          in unN n_g g

N (N f) r
 = forall x. N f x -> (x, r)
 = forall x. (forall y. f y -> (y, x)) -> (x, r)
 = forall x. exists y. (f y -> (y, x)) -> (x, r) -- move forall outside of ->
 = forall x. (f r -> (r, x)) -> (x, r)           -- instantiate y = r
 = forall x. (f r -> (x, r)) -> (x, r)
 = f r -- I'm not sure last transformation is correct

--------------------------------------------

Although it is already answered, I found another answer to the question by myself.

Type `N` was the RankNTypes-version of the type class Pairing, described in following articles.

[Free for DSLs, cofree for interpreters][1]

[Cofree Comonads and the Expression Problem][2]
(Paring is called Dual here)

Brief explanation of the Paring class
-------------------------------------

The definition of Paring is this.

> class Pairing f g where
>   pair :: (a -> b -> c) -> f a -> g b -> c

`f` and `N f` is Pairing.

> instance Pairing f (N f) where
>   pair k fa nb = uncurry k $ unN nb fa

N can be represented in terms of Paring.

> data Counterpart f r = forall g. Pairing f g => Counterpart (g r)
>
> iso1 :: N f r -> Counterpart f r
> iso1 = Counterpart
>
> iso2 :: Counterpart f r -> N f r
> iso2 (Counterpart gr) = N $ \fx -> pair (,) fx gr

There is a Free-vs-Cofree instance, that corresponds to my `unfree`.
Other interesting instances are also defined in the articles.

> instance Pairing f g => Pairing (Free f) (Cofree g) where
>   pair = undefined -- see link above

Former article [goes to][3] extending Pairing to do computation inside Monad m.

> class PairingM f g m | f -> g, g -> f where
>   pairM :: (a -> b -> m r) -> f a -> g b -> m r

If we rewrite PairingM to a form similar to N, we get the Object again.

> -- Monad m => HandleM' f m r ~ HandleM f m r
> data HandleM' f m r = forall g. PairingM f g m => HandleM' (g r)
> data HandleM f m r = HandleM { runHandleM :: forall x. f x -> m (x, r) }
>
> -- Fix (HandleM f m) ~ Object f m
> -- Free (HandleM f m) ~ (mortal Object from f to m)

  1: http://dlaing.org/cofun/posts/free_and_cofree.html
  2: http://comonad.com/reader/2008/the-cofree-comonad-and-the-expression-problem/
  3: http://dlaing.org/cofun/posts/pairing_over_the_network.html
