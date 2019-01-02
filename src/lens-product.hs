{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Data.Bifunctor

import Data.Reflection

data Lens s a = Lens
  { view :: s -> a
  , set :: a -> s -> s
  }

{-

A valid Lens is what satisfies the lens laws:
  * Get-Put: set l (view l s) s = s
  * Put-Get: view l (set l a s) = a
  * Put-Put: set l a (set l b s) = set l a s

-}

data Lens' s a = forall q. Eq q => Lens'
  { split   :: s -> (a,q)
  , unsplit :: (a,q) -> s
  }

{-

split and unsplit must witness the isomorphism.

  * unsplit . split = id
  * split . unsplit = id

-}

view' :: Lens' s a -> s -> a
view' Lens'{..} = fst . split

set' :: Lens' s a -> a -> s -> s
set' Lens'{..} a = unsplit . first (const a) . split

{-

(view' l, set' l) is valid Lens

  * Get-Put:

    set' l (view' l s) s
     = unsplit . first (const (fst . split $ s)) . split $ s
     = case split s of
         (a,q) -> case split s of
                    (a',_) -> unsplit (const a' a, q)
     = case split s of
         (a,q) -> unsplit (a,q)
     = unsplit (split s)
         -- unsplit . split = id
     = s

  * Put-Get:

    view' l (set' l a s)
     = fst . split . unsplit . first (const a) . split $ s
     = fst . first (const a) . split $ s
     = const a (fst (split s))
     = a

  * Put-Put:

    set' l a (set' l b s)
     = unsplit . first (const a) . split .
         unsplit . first (const b) . split $ s
     = unsplit . first (const a) . first (const b) . split $ s
     = unsplit . first (const a . const b) . split $ s
     = unsplit . first (const a) . split $ s
     = set' l a s
-}

newtype Sans s lens = Sans s

instance (Eq s, Reifies lens (Lens s a)) =>
         Eq (Sans s lens) where
  q1@(Sans s1) == Sans s2 =
    let Lens{..} = reflect q1
    in  s1 == set (view s1) s2

sans :: s -> proxy lens -> Sans s lens
sans s _ = Sans s

fromLens :: Eq s => Lens s a -> Lens' s a
fromLens l = reify l $ \lens ->
  let Lens{..} = reflect lens
  in  Lens' (\s -> (view s, s `sans` lens))
            (\(a, Sans s) -> set a s)

toLens :: Lens' s a -> Lens s a
toLens l' = Lens (view' l') (set' l')

{-

given lawful l :: Lens, fromLens l :: Lens' is valid.

  * unsplit . split = id

    unsplit (split s)
     = (\(a, Sans s) -> set a s) $ (view s, s `sans` lens)
     = set (view s) s
        -- Get-Put
     = s

  * split . unsplit = id

    split (unsplit (a, s `sans` l))
     = (view t, t `sans` l) where t = set a s
     = (a, t `sans` l)

    s `sans` l = t `sans` l
     <=>
    s = set (view s) t
      = set (view s) (set a s)
          -- Put-Put
      = set (view s) s
          -- Put-Get
      = s

It is easy to confirm:
  view' (fromLens l) = view l
  set' (fromLens l) = set l

  thus

  toLens . fromLens = id

-}

main :: IO ()
main = undefined
