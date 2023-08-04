{-# LANGUAGE DeriveFunctor #-}
module Applicative.MergedHead where

import Data.List.NonEmpty (NonEmpty(..))

-- | @MergedHead@ is an @Applicative@ formed by combining two list applicatives, @([] :: Type -> Type)@,
--   except that each half of the two lists shares the first element.
--
--   In category-theory-speak, @MergedHead@ is the pullback of two list applicatives along 'Data.Maybe.listToMaybe',
--   in the category of @Applicative@ morphisms.
--
--   >                   proj1
--   > MergedHead  ----------------> [ ]
--   >     |                          |
--   >     | proj2        listToMaybe |
--   >     |                          |
--   >     v                          v
--   >    [ ] --------------------> Maybe
--   >             listToMaybe
data MergedHead a = Zero | More a [a] [a]
    deriving (Show, Eq, Functor)

instance Applicative MergedHead where
    pure a = More a [] []
    Zero <*> _ = Zero
    _ <*> Zero = Zero
    More x xs1 xs2 <*> More y ys1 ys2 = More z zs1 zs2
      where
        z :| zs1 = (x :| xs1) <*> (y :| ys1)
        _ :| zs2 = (x :| xs2) <*> (y :| ys2)

-- | 'proj1' and 'proj2' are Applicative morphisms.
proj1, proj2 :: MergedHead a -> [a]
proj1 Zero = []
proj1 (More a as _) = a : as

proj2 Zero = []
proj2 (More a _ as) = a : as