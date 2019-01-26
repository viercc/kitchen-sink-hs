{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
module AutoLift(
  Reflected1(..),
  Reflected2(..),
  
  Show1(..),
  autoLiftShowsPrec, autoLiftShowList,
  autoLiftShowsPrec2, autoLiftShowList2,
  
  Read(..), Read1(..), ReadPrec,
  autoLiftReadPrec, autoLiftReadListPrec,
  autoLiftReadPrec2, autoLiftReadListPrec2
) where

import Data.Functor.Classes

import Data.Reflection
import Data.Proxy
import Data.Coerce
import Data.Bifunctor
import Text.Read

-- | AdHoc's instance is defined ad-hoc manner
newtype AdHoc s a = AdHoc { unAdHoc :: a }

{-

Uses technique taught from u/Iceland_jack

https://www.reddit.com/r/haskell_jp/comments/a75z0s/blog_reflection%E3%82%92%E4%BD%BF%E3%81%A3%E3%81%9F%E3%83%86%E3%82%AF%E3%83%8B%E3%83%83%E3%82%AF/ed3efcv/

-}
-- * Automatic Show1 and Show2

-- | Injected dictionary of Show
data ShowDict a = ShowDict
  { _showsPrec :: Int -> a -> ShowS
  , _showList :: [a] -> ShowS
  }

-- Instance of `AdHoc s a` is defined using injected dictionary.
instance (Reifies s (ShowDict a)) => Show (AdHoc s a) where
  showsPrec = coerce $ _showsPrec (reflect (Proxy @s))
  showList = coerce $ _showList (reflect (Proxy @s))

-- | Automatic Show1(liftShowsPrec) 
autoLiftShowsPrec ::
     forall f b. (forall xx yy. Coercible xx yy => Coercible (f xx) (f yy))
  => (forall a. Show a => Int -> f a -> ShowS)
  -> (Int -> b -> ShowS)
  -> ([b] -> ShowS)
  -> Int -> f b -> ShowS
autoLiftShowsPrec showsPrecFa showsPrecB showListB p fb =
  reify (ShowDict showsPrecB showListB) (body fb)

  where
    body :: forall name yy. Reifies name (ShowDict yy) => f yy -> Proxy name -> ShowS
    body as Proxy = showsPrecFa p (coerce @_ @(f (AdHoc name yy)) as)

-- | Automatic Show1(liftShowList) 
autoLiftShowList ::
     forall f b. (forall xx yy. Coercible xx yy => Coercible (f xx) (f yy))
  => (forall a. Show a => [f a] -> ShowS)
  -> (Int -> b -> ShowS)
  -> ([b] -> ShowS)
  -> [f b] -> ShowS
autoLiftShowList showListFa showsPrecB showListB fbs =
  reify (ShowDict showsPrecB showListB) (body fbs)

  where
    body :: forall name yy. Reifies name (ShowDict yy) => [f yy] -> Proxy name -> ShowS
    body as Proxy = showListFa (coerce @_ @[f (AdHoc name yy)] as)

-- | Automatic Show2(liftShowsPrec2)
autoLiftShowsPrec2 ::
     forall f c d.
       (forall x1 x2 y1 y2.
         (Coercible x1 y1, Coercible x2 y2) => Coercible (f x1 x2) (f y1 y2)
       )
  => (forall a b. (Show a, Show b) => Int -> f a b -> ShowS)
  -> (Int -> c -> ShowS)
  -> ([c] -> ShowS)
  -> (Int -> d -> ShowS)
  -> ([d] -> ShowS)
  -> Int -> f c d -> ShowS
autoLiftShowsPrec2 showsPrecFab
  showsPrecC showListC
  showsPrecD showListD
  p fcd =
  reify (ShowDict showsPrecC showListC) $ \proxyC ->
    reify (ShowDict showsPrecD showListD) $ \proxyD ->
      body proxyC proxyD

  where
    body :: forall name1 name2. (Reifies name1 (ShowDict c), Reifies name2 (ShowDict d))
         => Proxy name1 -> Proxy name2 -> ShowS
    body Proxy Proxy = showsPrecFab p (coerce @_ @(f (AdHoc name1 c) (AdHoc name2 d)) fcd)

-- | Automatic Show2(liftShowList2)
autoLiftShowList2 :: 
     forall f c d.
       (forall x1 x2 y1 y2.
         (Coercible x1 y1, Coercible x2 y2) => Coercible (f x1 x2) (f y1 y2)
       )
  => (forall a b. (Show a, Show b) => [f a b] -> ShowS)
  -> (Int -> c -> ShowS)
  -> ([c] -> ShowS)
  -> (Int -> d -> ShowS)
  -> ([d] -> ShowS)
  -> [f c d] -> ShowS
autoLiftShowList2 showListFab
  showsPrecC showListC
  showsPrecD showListD
  fcds =
  reify (ShowDict showsPrecC showListC) $ \proxyC ->
    reify (ShowDict showsPrecD showListD) $ \proxyD ->
      body proxyC proxyD

  where
    body :: forall name1 name2. (Reifies name1 (ShowDict c), Reifies name2 (ShowDict d))
         => Proxy name1 -> Proxy name2 -> ShowS
    body Proxy Proxy = showListFab (coerce @_ @[f (AdHoc name1 c) (AdHoc name2 d)] fcds)

-- * Automatic Read1 and Read2


-- | Injected dictionary of Read
data ReadDict a = ReadDict
  { _readPrec :: ReadPrec a
  , _readListPrec :: ReadPrec [a]
  }

instance (Reifies s (ReadDict a)) => Read (AdHoc s a) where
  readPrec = coerce $ _readPrec (reflect (Proxy @s))
  readListPrec = coerce $ _readListPrec (reflect (Proxy @s))

autoLiftReadPrec ::
     forall f b. (forall xx yy. Coercible xx yy => Coercible (f xx) (f yy))
  => (forall a. Read a => ReadPrec (f a))
  -> ReadPrec b
  -> ReadPrec [b]
  -> ReadPrec (f b)
autoLiftReadPrec readPrecFa readPrecB readListPrecB =
  reify (ReadDict readPrecB readListPrecB) body
  where
    body :: forall name. (Reifies name (ReadDict b)) => Proxy name -> ReadPrec (f b)
    body Proxy = coerce @(ReadPrec (f (AdHoc name b))) @_ readPrecFa

autoLiftReadListPrec :: 
     forall f b. (forall xx yy. Coercible xx yy => Coercible (f xx) (f yy))
  => (forall a. Read a => ReadPrec [f a])
  -> ReadPrec b
  -> ReadPrec [b]
  -> ReadPrec [f b]
autoLiftReadListPrec readListPrecFa readPrecB readListPrecB =
  reify (ReadDict readPrecB readListPrecB) body
  where
    body :: forall name. (Reifies name (ReadDict b)) => Proxy name -> ReadPrec [f b]
    body Proxy = coerce @(ReadPrec [f (AdHoc name b)]) @_ readListPrecFa

autoLiftReadPrec2
  :: forall f c d.
       (forall x1 x2 y1 y2.
         (Coercible x1 y1, Coercible x2 y2) => Coercible (f x1 x2) (f y1 y2)
       )
  => (forall a b. (Read a, Read b) => ReadPrec (f a b))
  -> ReadPrec c
  -> ReadPrec [c]
  -> ReadPrec d
  -> ReadPrec [d]
  -> ReadPrec (f c d)
autoLiftReadPrec2 readPrecFab
  readPrecC readListPrecC
  readPrecD readListPrecD =
    reify (ReadDict readPrecC readListPrecC) $ \proxyC ->
      reify (ReadDict readPrecD readListPrecD) $ \proxyD ->
        body proxyC proxyD
  where
    body :: forall name1 name2. (Reifies name1 (ReadDict c), Reifies name2 (ReadDict d))
      => Proxy name1 -> Proxy name2 -> ReadPrec (f c d)
    body Proxy Proxy = coerce @(ReadPrec (f (AdHoc name1 c) (AdHoc name2 d)))
                              @_
                              readPrecFab

autoLiftReadListPrec2
  :: forall f c d.
       (forall x1 x2 y1 y2.
         (Coercible x1 y1, Coercible x2 y2) => Coercible (f x1 x2) (f y1 y2)
       )
  => (forall a b. (Read a, Read b) => ReadPrec [f a b])
  -> ReadPrec c
  -> ReadPrec [c]
  -> ReadPrec d
  -> ReadPrec [d]
  -> ReadPrec [f c d]
autoLiftReadListPrec2 readListPrecFab
  readPrecC readListPrecC
  readPrecD readListPrecD =
    reify (ReadDict readPrecC readListPrecC) $ \proxyC ->
      reify (ReadDict readPrecD readListPrecD) $ \proxyD ->
        body proxyC proxyD

  where
    body :: forall name1 name2. (Reifies name1 (ReadDict c), Reifies name2 (ReadDict d))
      => Proxy name1 -> Proxy name2 -> ReadPrec [f c d]
    body Proxy Proxy = coerce @(ReadPrec [f (AdHoc name1 c) (AdHoc name2 d)])
                              @_
                              readListPrecFab

-----------------


newtype Reflected1 f a = Reflected1 (f a)

instance (forall a. Show a => Show (f a),
          forall xx yy. Coercible xx yy => Coercible (f xx) (f yy)) =>
         Show1 (Reflected1 f) where
  liftShowsPrec showsPrecB showListB p fb =
    autoLiftShowsPrec @f showsPrec showsPrecB showListB p (coerce fb)
  liftShowList showsPrecB showListB fbs =
    autoLiftShowList @f showList showsPrecB showListB (coerce fbs)

instance (forall a. Read a => Read (f a),
          forall xx yy. Coercible xx yy => Coercible (f xx) (f yy)) =>
         Read1 (Reflected1 f) where
  liftReadPrec readPrecB readListPrecB =
    coerce (autoLiftReadPrec @f readPrec readPrecB readListPrecB)

  liftReadListPrec readPrecB readListPrecB =
    coerce (autoLiftReadListPrec @f readListPrec readPrecB readListPrecB)

newtype Reflected2 f a b = Reflected2 (f a b)

instance (forall a b. (Show a, Show b) => Show (f a b),
          forall x1 y1 x2 y2.
            (Coercible x1 y1, Coercible x2 y2) => Coercible (f x1 x2) (f y1 y2)) =>
         Show2 (Reflected2 f) where
  liftShowsPrec2 showsPrecC showListC showsPrecD showListD p fcd =
    autoLiftShowsPrec2 @f showsPrec showsPrecC showListC showsPrecD showListD p
                       (coerce fcd)
  liftShowList2 showsPrecC showListC showsPrecD showListD fcds =
    autoLiftShowList2 @f showList showsPrecC showListC showsPrecD showListD (coerce fcds)

instance (forall a b. (Read a, Read b) => Read (f a b),
          forall x1 y1 x2 y2.
            (Coercible x1 y1, Coercible x2 y2) => Coercible (f x1 x2) (f y1 y2)) =>
         Read2 (Reflected2 f) where
  liftReadPrec2 readPrecC readListPrecC readPrecD readListPrecD =
    coerce (autoLiftReadPrec2 @f
              readPrec
              readPrecC readListPrecC readPrecD readListPrecD)

  liftReadListPrec2 readPrecC readListPrecC readPrecD readListPrecD =
    coerce (autoLiftReadListPrec2 @f
              readListPrec
              readPrecC readListPrecC readPrecD readListPrecD)
