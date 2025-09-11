{-

https://mobile.twitter.com/lexi_lambda/status/1192930938537332736?s=19

-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE TypeApplications, TypeAbstractions #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

module ExcludedMiddle where

import Data.Void (Void, absurd)

-- The question is whether `goal` is possible to write for a type `T`.
--
-- @
-- goal :: forall f a b. (Functor f) => ((T -> a) -> b) -> (T -> f a) -> f b
-- goal = _
-- @

-- Let's define the type of the goal as a type parameterized by `T`.
type Goal t = forall f a b. (Functor f) => ((t -> a) -> b) -> (t -> f a) -> f b

-- It's sometimes possible. For example, if we /knew/ `T` is inhabited,
-- there's an implementation of `goal`.
--
-- @
-- t :: T
-- 
-- goal1 :: Goal T
-- goal1 f g = fmap (\a -> f (const a)) (g t)
-- @

-- By representing "`t` is inhabited" using a value of `t`, `goal1` can be written as below:
goal1 :: forall t. t -> Goal t
goal1 t f g = fmap (\a -> f (const a)) (g t)

-- But if `T` is unhabited, i.e. `T` is isomorphic to `Void`,
-- it's not. See the following calculation:
--
-- >    Goal T
-- >  = ((T -> a) -> b) -> (T -> f a) -> f b
-- >  ~ ((Void -> a) -> b) -> (Void -> f a) -> f b
-- >  ~ (() -> b) -> () -> f b
-- >  ~ b -> f b
--
-- It turns out we need a function of type `(_ :: ∀b. b -> f b)`,
-- but it is not always possible for an arbitrary `Functor f`.
--
-- This answers the initial question: it's not always possible.
-- Probably I may stop here, but let's delve into more!

-- Assuming more constraint on `f`, for example `Applicative f`, it's possible.

type Goal' t = forall f a b. (Applicative f) => ((t -> a) -> b) -> (t -> f a) -> f b

-- Given we knew `T` is empty, as in
--
-- @
-- not_t :: T -> Void
-- not_t = _
-- @
--
-- , we can have modified goal.
--
-- @
-- goal2 :: Goal' T
-- goal2 f _ = pure (f (absurd . not_t))
-- @

-- By representing "`t` is empty" using `Not t ~ t -> Void`,
-- `goal2` can be written as below:

type Not t = t -> Void
goal2 :: forall t. Not t -> Goal' t
goal2 not_t f _ = pure (f (absurd . not_t))

-- Combining the above two cases, if we knew `T` is either inhabited or empty,
-- then we have implementation for `Applicative f`.

-- Let's represent "we knew either" as `Decide t` type.
-- `Decide t` is defined indirectly using `Question` for later convenience.

type Decide t = Question t Void
data Question t a = Yes t | No (t -> a)

-- Then:

goal3 :: forall t. Decide t -> Goal' t
goal3 (Yes t)    = goal1 t
goal3 (No not_t) = goal2 not_t

-- Is it possible to define `Applicative` version of the goal
-- without requiring any constraint like `Decide` on `t`?
--
-- The answer is no. There is a known fact that we can't
-- write a program which implements `Decide t` for
-- unconstrained `t`.
-- In other words, there's no term of type `forall t. Decide t`.
--
-- It is called the /law of excluded middle/.

type ExcludedMiddle = forall t. Decide t

-- But we can show `Goal' t` implies `Decide t`!
-- Therefore, if we had `forall t. Goal' t`,
-- `ExcludedMiddle` can be constructed, which is contradiction.

-- To prove `Goal' t` implies `Decide t`, let's 
-- show that `Question t` can be `Applicative`. 

instance Functor (Question t) where
  fmap f question = case question of
    Yes t -> Yes t
    No g  -> No (f . g)

instance Applicative (Question t) where
  pure a = No (const a)
  Yes t <*> _ = Yes t
  _ <*> Yes t = Yes t
  No g <*> No h = No (\t -> g t (h t))

-- By specializing `Applicative f` in the `Goal' t` to `Question t`,
-- we get to implement `Goal' t -> Decide t`.

goal'2decide :: forall t. Goal' t -> Decide t
goal'2decide @t goal' =
  aux (goal' @(Question t) @Void @(Not t) id Yes)
  
  -- > Goal' t
  -- >  ~  forall f a b. (Applicative f) => ((t -> a) -> b) -> (t -> f a) -> f b
  -- >  <: forall a b. ((t -> a) -> b) -> (t -> Question t a) -> Question t b
  -- >  <: forall b. ((t -> Void) -> b) -> (t -> Question t Void) -> Question t b
  -- >  ~  forall b. (Not t       -> b) -> (t -> Question t Void) -> Question t b
  -- >  <: (Not t -> Not t) -> (t -> Question t Void) -> Question t (Not t)

  where
    -- Either `u` or `u -> Not u`
    --   =>
    -- Either `u` or `Not u`
    aux :: forall u. Question u (Not u) -> Decide u
    aux q = case q of
      Yes u -> Yes u
      No f -> No (\u -> f u u)
