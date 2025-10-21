{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module Partial.Monad(
  PMonad(..), pjoin, pmapDefault,

  Pt(..)
) where

import Prelude hiding (id, (.))
import Control.Category (Category(..))

import Partial
import Partial.Functor
import Control.Arrow (Arrow(..))
import Control.Monad (join, ap)
import Data.List.NonEmpty (NonEmpty)
import Data.Functor.Product (Product (..))
import Data.Functor.These (These1 (..))
import Data.These
import Data.Coerce (coerce)
import Data.Boring (Absurd)
import Data.Functor.Const (Const)

-- | Monad on 'Partial'.
-- 
-- ==== Laws
-- 
-- An instance of @PMonad@ must satisfy these laws.
-- 
-- - /right unit/
--
--     @
--     pbind ppure === id
--     @
--
-- - /left unit/
--
--     @
--     pbind f . ppure === f
--     @
--
-- - /associativity/
--
--     @
--     pbind f . pbind g === pbind (pbind f . g)
--     @
-- 
-- - /naturality of ppure/
--
--     @
--     pmap f . ppure === ppure . f
--     @
--
-- - /naturality of pbind/
--
--     @
--     pmap f . pbind g === pbind (pmap f . g)
--     @
-- 
-- With these laws, it can be shown that @'pmap'@ must be
-- equivalent to the following ('pmapDefault').
-- 
-- @
-- pmap :: (a -? b) -> (m a -? m b)
-- pmap f === pmapDefault f === pbind (ppure . f)
-- @
-- 
-- Conversely, with the first three laws (left and right unit law, associativity) plus
-- @pmap === pmapDefault@ shows /naturality of ppure/ and /naturality of pbind/.
-- Therefore, one may instead show the first three laws + @pmap === pmapDefault@ to
-- prove their @PMonad@ instance is valid.

{-

[NOTE: pmapDefault]

@(pbind, ppure)@ determines @pmap@:

- /default pmap/: 

  > pmap f === pbind (ppure . f)

> (proof)
> pmap f
>   === pmap f . id
>     {right unit}
>   === pmap f . pbind ppure
>     {naturality of pbind}
>   === pbind (pmap f . ppure)
>     {naturality of ppure}
>   === pbind (ppure . f)

Conversely, from left and right unit laws, associativity, and default @pmap@,
two naturality condition follows.

> (proof:ppure-naturality)
> pmap f . ppure
>     {default pmap}
>   === pbind (ppure . f) . ppure
>     {right unit}
>   === ppure . f

> (proof:pbind-naturality)
> pmap f . pbind g
>     {default pmap}
>   === pbind (ppure . f) . pbind g
>     {associativity}
>   === pbind (pbind (ppure . f) . g)
>     {default pmap}
>   === pbind (pmap f . g)


-}
class (PFunctor m) => PMonad m where
  ppure :: a -? m a
  pbind :: (a -? m b) -> m a -? m b

-- | > pjoin = pbind id
pjoin :: PMonad m => m (m a) -? m a
pjoin = pbind id

-- | @pmap@ can be implemented using only @ppure@ and @pbind@.
--   (same to the relation between 'fmap' and 'Control.Mona.liftM') 
pmapDefault :: PMonad m => (a -? b) -> (m a -? m b)
pmapDefault f = pbind (ppure . f)

-- | @PMonad m@ induces @Monad@ structure on @Maybe (m _)@.
newtype Pt m a = Pt { unPt :: Maybe (m a) }
  deriving (Show, Eq, Functor)

instance PMonad m => Applicative (Pt m) where
  pure = kleisliPt ppure
  (<*>) = ap

instance PMonad m => Monad (Pt m) where
  Pt ma >>= k = Pt $ ma >>= runPartial (pbind (unkleisliPt k))

kleisliPt :: (a -? m b) -> a -> Pt m b
kleisliPt = coerce

unkleisliPt :: (a -> Pt m b) -> (a -? m b)
unkleisliPt = coerce

instance PMonad Maybe where
  ppure = arr pure
  pbind k = arr join . pmap k

-- >>> mxs = [Pt Nothing, Pt (Just Nothing), Pt (Just (Just 'x'))] :: [Pt Maybe Char]
-- >>> [mx >>= \x -> my >>= \y -> pure [x,y] | mx <- mxs, my <- mxs ]
-- [Pt {unPt = Nothing},      Pt {unPt = Nothing},      Pt {unPt = Nothing},
--  Pt {unPt = Just Nothing}, Pt {unPt = Just Nothing}, Pt {unPt = Just Nothing},
--  Pt {unPt = Nothing},      Pt {unPt = Just Nothing}, Pt {unPt = Just (Just "xx")}
-- ]

-- | @Pt (Either a) ~ Either (Maybe a)@
instance PMonad (Either a) where
  ppure = arr pure
  pbind k = arr join . pmap k

-- | @Pt ((,) a) ~ WriterT a Maybe@
instance Monoid a => PMonad ((,) a) where
  ppure = arr pure
  pbind k = arr join . pmap k

-- | @Pt (These a) ~ MaybeT (Writer (Maybe a))@
instance Semigroup a => PMonad (These a) where
  ppure = arr pure
  pbind k = arr join . pmap k

-- | @Pt (Const Void) ~ Proxy@
instance Absurd a => PMonad (Const a) where
  ppure = zero
  pbind _ = zero

{-

[NOTE: Lifted PMonad ]

Whenever @ppure, pbind@ is based off of @Monad@ like above instances,
i.e.

- @ppure = arr pure@
- @pbind k = arr join . pmap k@

Let's call such @PMonad@ a \"lifted\" PMonad.

For a lifted PMonad, the first three laws follows from the two naturality laws.
For example, associativity can be shown as the following.

  pbind f . pbind g
   = arr join . pmap f . pbind g
      {naturality of pbind}
   = arr join . pbind (pmap f . g)
   = arr join . arr join . pmap (pmap f . g)
   = arr (join . join) . pmap (pmap f . g)
      {Monad law(associativity)}
   = arr (join . fmap join) . pmap (pmap f . g)
   = arr join . arr (fmap join) . pmap (pmap f . g)
      {plain functor}
   = arr join . pmap (arr join) . pmap (pmap f) . pmap g
   = arr join . pmap (arr join . pmap f . g)
   = arr join . pmap (pbind f . g)
   = pbind (pbind f . g)

Left and right unit laws can be done similarly.

-}

{-

[NOTE: Lifted and Traversable-based ]

For a lifted @PMonad@ (@ppure, pjoin@ are defined by @Monad@),
the previous note explains naturality conditions imply other three laws.

If its @PFunctor@ instance is defined as
@pmap f = smash f = Partial (traverse f)@, the converse also hold.
For such @PMonad@, the first three laws (left and right unit, associativity) imply
two naturality laws.

The reason is, for such @PMonad@, @pmap = pmapDefault@ always hold, and as
[Note: pmapDefault] explains, (pmap = pmapDefault && the first three) implies naturality laws.

  (proof)
  @pmap = pmapDefault@ can be written as an unwrapped version:

    traverse f = fmap join . traverse (fmap pure . f)

  And this is true by the following computation.

    fmap join . traverse (fmap pure . f)
    === fmap join . fmap (fmap pure) . traverse f
    === fmap (join . fmap pure) . traverse f
    === traverse f

-}

instance PMonad NonEmpty where
  ppure = arr pure
  pbind k = arr join . pmap k

{-

This is a "lifted" case, thus showing only naturality
suffice.

* Instead of directly prove naturality of pbind,
  the following auxiliary equation (A) can be proven:

    (A) pmap f . arr join === arr join . pmap (pmap f)

  because

    pmap f . pbind g
      {definition of pbind}
    = pmap f . arr join . pmap g
      {use (A)}
    = pjoin . pmap (pmap f) . pmap g
    = pjoin . pmap (pmap f . pmap g)
      {definition of pbind}
    = pbind (pmap f . g)

* To avoid wrapping/unwrapping of @Partial@ clutters the proof,
  define the unwrapped versions as below:

  @
  pmap' :: (a -> Maybe b) -> NonEmpty a -> Maybe (NonEmpty b)
  pmap' f = nonEmpty . mapMaybe f . toList
  @

  By performing unwrapping, naturality laws can be written as:

  - naturality of ppure:

    @
    pmap' f . pure === fmap pure . f
    @

  - equation (A) (for naturality of pjoin):

    @
    pmap' f . join === fmap join . pmap' (pmap' f)
    @

[naturality of ppure]

pmap' f . pure
 = nonEmpty . mapMaybe f . toList . pure
 = \a -> nonEmpty (mapMaybe f [a])
 = \a -> case f a of
    Nothing -> Nothing
    Just b  -> Just (pure b)
 = fmap pure . f

[(A) for naturality of pbind]

pmap' f . join
 = nonEmpty . mapMaybe f . toList . join
   { (toList :: NonEmpty ~> []) is a monad morphism }
 = nonEmpty . mapMaybe f . join . fmap toList . toList
   {
     mapMaybe f . join
      = (join . fmap (maybeToList . f)) . join
      = join . join . fmap (fmap (maybeToList . f))
      = join . fmap (join . fmap (maybeToList . f))
      = join . fmap (mapMaybe f)
   }
 = nonEmpty . join . fmap (mapMaybe f) . fmap toList . toList
 = nonEmpty . join . fmap (mapMaybe f . toList)      . toList
  {
    unNonEmpty . nonEmpty = id
      where
        unNonEmpty :: Maybe (NonEmpty a) -> [a]
        unNonEmpty = join . fmap toList . maybeToList
    unNonEmpty (nonEmpty [])
      = unNonEmpty Nothing
      = join (fmap toList []) = []
    unNonEmpty (nonEmpty (xs : xss))
      = unNonEmpty (Just (xs :| xss))
      = join $ fmap toList [xs :| xss]
      = join [ xs : xss ]
      = xs : xss
  }
 = nonEmpty . join . fmap (unNonEmpty . nonEmpty . mapMaybe f . toList) . toList

 = nonEmpty . join . fmap (unNonEmpty . pmap' f) . toList
 
 = nonEmpty . join . fmap join . fmap (fmap toList)
     . fmap (maybeToList . pmap' f) . toList
 
 = nonEmpty . join . join . fmap (fmap toList)
     . fmap (maybeToList . pmap' f) . toList
 
 = nonEmpty . join . fmap toList . join
     . fmap (maybeToList . pmap' f) . toList
   { join . fmap (maybeToList . g) = mapMaybe g }
 = nonEmpty . join . fmap toList
     . mapMaybe (pmap' f) . toList
   { (B) }
 = fmap join . nonEmpty . mapMaybe (pmap' f) . toList
 = fmap join . pmap' (pmap' f)

(B) nonEmtpy . join . fmap toList = fmap join . nonEmpty
        :: [NonEmpty a] -> Maybe (NonEmpty a)

  (proof)
  case analysis on outer list:

    nonEmpty (join (fmap toList []))
    = nonEmpty (join [])
    = nonEmpty []
    = Nothing
    = fmap join Nothing
    = fmap join (nonEmpty [])

    nonEmpty (join (fmap toList (xs : xss)))
    = nonEmpty (join (fmap toList (toList (xs :| xss))))
    = nonEmpty (toList (join (xs :| xss)))
      -- nonEmpty . toList = Just
    = Just (join (xs :| xss))
    = fmap join (Just (xs : xss))
    = fmap join (nonEmpty (xs : xss))

-}

instance (PMonad t, PMonad u) => PMonad (Product t u) where
  ppure = Partial $ \a ->
    Pair <$> runPartial ppure a
         <*> runPartial ppure a
  pbind k = Partial $ \(Pair ta ua) ->
    Pair <$> runPartial (pbind (proj1 . k)) ta
         <*> runPartial (pbind (proj2 . k)) ua
    where
      proj1 :: Product t u x -? t x
      proj1 = arr $ \(Pair tx _) -> tx
      proj2 :: Product t u x -? u x
      proj2 = arr $ \(Pair _ ux) -> ux

instance (PMonad t, PMonad u) => PMonad (These1 t u) where
  ppure = arr wrapThese1 . ppair ppure ppure
  pbind k = arr wrapThese1
    . bipmapThese (pbind k1) (pbind k2)
    . arr unwrapThese1
    where
      k1 = pfst . arr unwrapThese1 . k
      k2 = psnd . arr unwrapThese1 . k

unwrapThese1 :: These1 t u a -> These (t a) (u a)
unwrapThese1 tu = case tu of
  This1 ta -> This ta
  That1 ua -> That ua
  These1 ta ua -> These ta ua

wrapThese1 :: These (t a) (u a) -> These1 t u a
wrapThese1 tu = case tu of
  This ta -> This1 ta
  That ua -> That1 ua
  These ta ua -> These1 ta ua
