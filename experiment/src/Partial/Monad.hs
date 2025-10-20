{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module Partial.Monad where

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
class (PFunctor m) => PMonad m where
  ppure :: a -? m a
  pbind :: (a -? m b) -> m a -? m b

-- | > pjoin = pbind id
pjoin :: PMonad m => m (m a) -? m a
pjoin = pbind id

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

instance PMonad (Either a) where
  ppure = arr pure
  pbind k = arr join . pmap k

instance Monoid a => PMonad ((,) a) where
  ppure = arr pure
  pbind k = arr join . pmap k


{-

[NOTE: You can use usual @Monad@ natural with respect to @pmap@]

Whenever @ppure, pbind@ is based off of @Monad@ like above instances,
i.e.

- @ppure = arr pure@
- @pbind k = arr join . pmap k@

You only need to check naturality conditions. For example,
right unit law can be shown as the following.

  pbind ppure
   = arr join . pmap ppure
   = arr join . pmap (arr pure)
   = arr join . arr (fmap pure)
   = arr (join . fmap pure)
   = arr id
   = id

Left unit and associativity law can be done similarly.

-}

{-

[NOTE: Using @Monad@ and @Traverseable@]

For a @PMonad@ with @ppure, pjoin@ defined using plain @Monad@
as previous note, if its @PFunctor@ instance is defined as
@pmap = smash@ using 'traverse', naturality conditions reduces to
following equations.

(2) traverse f . pure === fmap pure . f
(3) traverse f . join === fmap join . traverse (traverse f)

Note that @traverse f . pure === fmap pure . f@ hold
if @pure x@ does not discard 'x',
i.e. anything except 'Data.Proxy.Proxy' monad.

    (lemma) Since @sequenceA (pure Nothing) === Just _@
    implies @pure Nothing@ does not use @Nothing@ to construct its value.
    Therefore, if @pure x@ does depend on @x@, @sequenceA (pure Nothing) === Nothing@.

    (proof)
    traverse f (pure a)
     = sequenceA (fmap f (pure a))
     = sequenceA (pure (f a))
     = case f a of
         Nothing -> sequenceA (pure Nothing)
         Just b  -> sequenceA (pure (Just b))
     = case f a of
         Nothing -> Nothing
         Just b  -> sequenceA . fmap Just (pure b)
     = case f a of
         Nothing -> Nothing
         Just b  -> Just (pure b)
     = fmap pure (f a)

[naturality of ppure]

pmap (Partial f) . ppure
 = Partial (traverse f) . Partial (Just . pure)
 = Partial (traverse f <=< Just . pure)
 = Partial (traverse f . pure)
 = Partial $ fmap pure . f
 = Partial $ Just . pure <=< f
 = arr pure . Partial f
 = ppure . Partial f

[naturality of pbind]

pmap (Partial f) . pbind (Partial g)
 = pmap (Partial f) . arr join . pmap (Partial g)
 = Partial (traverse f) . Partial (Just . join) . Partial (traverse g)
 = Partial (traverse f <=< Just join <=< traverse g)
 = Partial (traverse f . join <=< traverse g)
 = Partial (fmap join . traverse (traverse f) <=< traverse g)
 = Partial (fmap join . (traverse (traverse f) <=< traverse g))
   -- If the @Monad@ instance used for (<=<) is a commutative monad,
   --   @traverse f1 <=< traverse f2 === traverse (f1 <=< f2)@
   -- hold. The (<=<) used here is @Monad Maybe@ which is commutative.
 = Partial (fmap join . traverse (traverse f <=< g))
 = Partial (Just join <=< traverse (traverse f <=< g))
 = arr join . pmap (Partial (traverse f <=< g))
 = arr join . pmap (pmap (Partial f) . g)
 = pbind (pmap (Partial f) . g)

-}

instance PMonad NonEmpty where
  ppure = arr pure
  pbind k = arr join . pmap k

{-

This is "using usual Monad" case, thus showing only naturality
suffice.

[naturality of ppure]

pmap (Partial f) . ppure
 = Partial (nonEmpty . mapMaybe f . toList) . Partial (Just . singleton)
 = Partial (nonEmpty . mapMaybe f . toList <=< Just . singleton)
 = Partial (nonEmpty . mapMaybe f . toList . singleton)
 = Partial (\a -> nonEmpty (mapMaybe f [a]))
 = Partial $ \a -> case f a of
    Nothing -> Nothing
    Just b  -> Just (singleton b)
 = Partial $ fmap singleton . f
 = Partial $ Just . singleton <=< f
 = ppure . Partial f

[naturality of pbind]

instead prove naturality of pjoin

  pmap f . pjoin === pjoin . pmap (pmap f)

which implies naturality of pbind

  pmap f . pbind g
   = pmap f . pjoin . pmap g
   = pjoin . pmap (pmap f) . pmap g
   = pjoin . pmap (pmap f . pmap g)
   = pbind (pmap f . g)

pmap (Partial f) . pjoin
 = pmap (Partial f) . arr join
 = Partial (nonEmpty . mapMaybe f . toList) . Partial (Just . join) . Partial (nonEmpty . mapMaybe g . toList)
 = Partial $
    nonEmpty . mapMaybe f . toList <=< Just . join
 = Partial $
    nonEmpty . mapMaybe f . toList . join
 = Partial $
    nonEmpty . mapMaybe f . join . fmap toList . toList
   -- mapMaybe f . join
   --  = (join . fmap (maybeToList . f)) . join
   --  = join . join . fmap (fmap (maybeToList . f))
   --  = join . fmap (join . fmap (maybeToList . f))
   --  = join . fmap (mapMaybe f)
 = Partial $
    nonEmpty . join . fmap (mapMaybe f) . fmap toList . toList
 = Partial $
    nonEmpty . join . fmap (mapMaybe f . toList) . toList
 = Partial $
    nonEmpty . join . fmap (unNonEmpty . nonEmpty . mapMaybe f . toList) . toList
      where unNonEmpty = maybe [] toList = join . fmap toList . maybeToList
 = Partial $
    nonEmpty . join . fmap join . fmap (fmap toList . maybeToList)
      . fmap (nonEmpty . mapMaybe f . toList) . toList
 = Partial $
    nonEmpty . join . join . fmap (fmap toList)
      . fmap (maybeToList . nonEmpty . mapMaybe f . toList) . toList

 = Partial $
    nonEmpty . join . fmap toList
      . join . fmap (maybeToList . nonEmpty . mapMaybe f . toList) . toList
 = Partial $
    nonEmpty . join . fmap toList
      . mapMaybe (nonEmpty . mapMaybe f . toList) . toList

   -- (*)

 = Partial $
    fmap join . nonEmpty
      . mapMaybe (nonEmpty . mapMaybe f . toList) . toList
 = arr join . pmap (Partial (nonEmpty . mapMaybe f . toList))
 = arr join . pmap (pmap f)

(*)

nonEmtpy . join . fmap toList
  === fmap join . nonEmpty    :: [NonEmpty a] -> Maybe (NonEmpty a)

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
