{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
module ThesePair where

import Data.These (These(..))

type MyType a b c d e =
   (Maybe a, Maybe b, Maybe c, Maybe d, Maybe e)

type (:?:) = These
infixl 3 :?:

-- Maybe (MyType' a b c d e) is isomorphic to (MyType a b c d e)
type MyType' a b c d e = (a :?: b :?: c :?: d :?: e)

-- Isomorphism
theseMaybes :: (Maybe a, Maybe b) -> Maybe (These a b)
theseMaybes = \case
    (Nothing, Nothing) -> Nothing
    (Just a, Nothing) -> Just (This a)
    (Nothing, Just b) -> Just (That b) 
    (Just a, Just b) -> Just (These a b)

maybeThese :: Maybe (These a b) -> (Maybe a, Maybe b)
maybeThese = \case
    Nothing -> (Nothing, Nothing)
    Just (This a) -> (Just a, Nothing)
    Just (That b) -> (Nothing, Just b)
    Just (These a b) -> (Just a, Just b)

-- Isomorphism, too
theseMaybes5 :: MyType a b c d e -> Maybe (MyType' a b c d e)
theseMaybes5 (ma, mb, mc, md, me) = (((ma ? mb) ? mc) ? md) ? me
  where mx ? my = theseMaybes (mx, my)

maybeThese5 :: Maybe (MyType' a b c d e) -> MyType a b c d e
maybeThese5 mabcde  =
   let (mabcd, me) = maybeThese mabcde
       (mabc, md) = maybeThese mabcd
       (mab, mc) = maybeThese mabc
       (ma, mb) = maybeThese mab
   in (ma, mb, mc, md, me)
