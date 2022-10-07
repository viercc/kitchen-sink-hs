> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
> {-# LANGUAGE ConstraintKinds #-}
> module Monad.FreeAny where
>
> import Control.Monad

Free something

> newtype Free c a = Free { runFree :: forall r. c r => (a -> r) -> r }

Adjunction witness

> adj1 :: c b => (a -> b) -> Free c a -> b
> adj1 g fa = runFree fa g
> 
> -- first argument must be @c@-homomorphism
> adj2 :: (Free c a -> b) -> (a -> b)
> adj2 h a = h (Free (\k -> k a))

Free is a Functor, Applicative and Monad.

> instance Functor (Free c) where
>   fmap f (Free h) = Free $ \k -> h (k . f)
> instance Applicative (Free c) where
>   pure a = Free $ \k -> k a
>   (<*>) = ap
> instance Monad (Free c) where
>   ma >>= f = Free $ \k -> runFree ma (\a -> runFree (f a) k)

"Free Monoid" is indeed free monoid.

> instance Semigroup (Free Monoid a) where
>   a <> b = Free $ \f -> runFree a f <> runFree b f
> instance Monoid (Free Monoid a) where
>   mempty      = Free $ \_ -> mempty

We can use any type class 'c :: * -> Constraint', so one can try Num.

> liftOp0 :: (forall r. c r => r) -> Free c a
> liftOp0 constant = Free (\_ -> constant)
> liftOp1 :: (forall r. c r => r -> r) -> Free c a -> Free c a
> liftOp1 op1 a = Free (\k -> op1 (runFree a k))
> liftOp2 :: (forall r. c r => r -> r -> r) -> Free c a -> Free c a -> Free c a
> liftOp2 op2 a b = Free (\k -> op2 (runFree a k) (runFree b k))
> 
> instance Num (Free Num a) where
>   fromInteger n = liftOp0 (fromInteger n)
>   (+) = liftOp2 (+)
>   (-) = liftOp2 (-)
>   (*) = liftOp2 (*)
>   abs = liftOp1 abs
>   signum = liftOp1 signum
