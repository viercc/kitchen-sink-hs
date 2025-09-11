{-

https://mobile.twitter.com/lexi_lambda/status/1192930938537332736?s=19

-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

module ExcludedMiddle where

import Data.Void (Void, absurd)

-- The question is whether it is possible to write a function of
-- the type below, for a type `T`.
--
-- @
-- forall f a b. (Functor f) => ((T -> a) -> b) -> (T -> f a) -> f b
-- @
-- 
-- By Yoneda lemma, it can be simplified to:
--
-- @
-- goal :: forall f a. (Functor f) => (T -> f a) -> f (T -> a)
-- @
-- 
-- Let's define the type of the goal as a type parameterized by `T`.
type Goal t = forall f a. (Functor f) => (t -> f a) -> f (t -> a)

-- It's sometimes possible. For example, if we /knew/ `T` is inhabited,
-- there's an implementation of `goal`.
--
-- @
-- t :: T
--
-- goal1 :: Goal T
-- goal1 g = const <$> g t
-- @

-- By representing "`t` is inhabited" using a value of `t`, `goal1` can be written as below:
goal1 :: forall t. t -> Goal t
goal1 t g = const <$> g t

-- But if `T` is unhabited, i.e. `T` is isomorphic to `Void`,
-- it's not. See the following calculation:
--
-- >    Goal T
-- >  = (T -> f a) -> f (T -> a)
-- >  ~ (Void -> f a) -> f (Void -> a)
-- >  ~ () -> f ()
-- >  ~ f ()
--
-- It turns out we need a value of type `f ()`,
-- but it is not always possible for an arbitrary `Functor f`.
--
-- This answers the initial question: it's not always possible.
-- Probably I may stop here, but let's delve into more!

-- Let's modify the goal to by assuming more constraint on `f`,
-- for example `Applicative f`, to be able to use `pure () :: f ()`.

type Goal' t = forall f a. (Applicative f) => (t -> f a) -> f (t -> a)

-- Given we knew `T` is empty, as in `not_t`, we can have the modified `Goal' T`.
--
-- @
-- not_t :: T -> Void
-- not_t = _
-- 
-- goal2 :: Goal' T
-- goal2 _ = pure (absurd . not_t)
-- @

-- By representing "`t` is empty" using `Not t ~ t -> Void`,
-- `goal2` can be written as below:

type Not t = t -> Void

goal2 :: forall t. Not t -> Goal' t
goal2 not_t _ = pure (absurd . not_t)

-- Combining the above two cases, if we knew `T` is either inhabited or empty,
-- then we have implementation for `Applicative f`.

-- Let's represent "we knew either" as `Decide t` type.
-- `Decide t` is defined indirectly using `Question` for later convenience.

type Decide t = Question t Void

data Question t a = Yes t | No (t -> a)

-- Then:

goal3 :: forall t. Decide t -> Goal' t
goal3 (Yes t) = goal1 t
goal3 (No not_t) = goal2 not_t

-- Converse of `goal3` also holds, using `Applicative (Question t)` instance.
-- Therefore, `Goal' t` is equivalent to `Decide t`.

goal3Converse :: forall t. Goal' t -> Decide t
goal3Converse @t goal' =
  aux (goal' @(Question t) @Void Yes)
  where
    {-
    Goal' t
      ~  forall f a. (Applicative f) => (t -> f a) -> f (t -> a)
      <: forall a. (t -> Question t a) -> Question t (t -> a)
      <: (t -> Question t Void) -> Question t (t -> Void)
      ~  (t -> Question t Void) -> Question t (Not t)
    -}

    -- (Either `u` or `u -> Not u`)
    --   =>
    -- (Either `u` or `Not u`)
    aux :: forall u. Question u (Not u) -> Decide u
    aux q = case q of
      Yes u -> Yes u
      No f -> No (\u -> f u u)

-- Note:
--   This was "the later convenience." `goal3Converse` was a function which uses `Goal' t`
--   to construct a `Question t Void` value.
--   Since `Question t Void` means "there's either a value of `t` or `t -> Void`" and
--   `t -> Void = Not t`, it's easy to define `Decide t` as `Question t Void`,
--   rather than the other type isomorphic to it.

instance Functor (Question t) where
  fmap f question = case question of
    Yes t -> Yes t
    No g -> No (f . g)

instance Applicative (Question t) where
  pure a = No (const a)
  Yes t <*> _ = Yes t
  _ <*> Yes t = Yes t
  No g <*> No h = No (\t -> g t (h t))

-- This equivalence shows it is not possible to write
-- `forall t. Goal' t` function, which has no constraint on `t`.
--
-- There is a known fact that we can't write a program which implements `Decide t` for
-- unconstrained `t`.
-- In other words, there's no term of type `forall t. Decide t`.
-- It is called the /law of excluded middle/, because when we see this type
-- as a proposition, it means "for any proposition `t`, either `t` or `Not t` holds."

type ExcludedMiddle = forall t. Decide t

-- If we had `forall t. Goal' t`, we can construct a value (=proof) of `ExcludedMiddle`,
-- which is known to be impossible.