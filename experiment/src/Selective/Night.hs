{-

Selective Applicative Functors
https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf

Comments on Reddit
https://www.reddit.com/r/haskell/comments/axje88/selective_applicative_functors/ehwo9qn/

-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
module Selective.Night where

import Prelude hiding ((.), id)
import Control.Category

-- | Function + distinguished constant
data a -? b = Const b | Fun (a -> b)
  deriving Functor
infixr 0 -?

composeS :: (b -? c) -> (a -? b) -> (a -? c)
composeS (Const c) _ab       = Const c
composeS (Fun bc)  (Const b) = Const (bc b)
composeS (Fun bc)  (Fun ab)  = Fun (bc . ab)

instance Category (-?) where
  id = Fun id
  (.) = composeS

{-

[Category laws check]

Fun id . Const a = Const (id a)  = Const a
Fun id . Fun ab  = Fun (id . ab) = Fun ab

Const a . Fun id                 = Const a
Fun ab  . Fun id = Fun (ab . id) = Fun ab

(Const d .  bc) . ab  = Const d . ab = Const d
 Const d . (bc  . ab) = Const d

(Fun cd .  Const c) . ab  = Const (cd c)
 Fun cd . (Const c  . ab) = Fun cd . Const c = Const (cd c)

(Fun cd .  Fun bc) . Const b  = Const ((cd . bc) b)
 Fun cd . (Fun bc  . Const b) = Const (cd (bc b))

(Fun cd .  Fun bc) . Fun ab  = Fun (cd . bc . ab)
 Fun cd . (Fun bc .  Fun ab) = Fun (cd . bc . ab)

-}

fstS :: (a, b) -? a
fstS = Fun fst

sndS :: (a, b) -? b
sndS = Fun snd

pairS :: (z -? x) -> (z -? y) -> z -? (x, y)
pairS (Const x) (Const y) = Const (x, y)
pairS (Fun zx)  (Const y) = Fun $ \z -> (zx z, y)
pairS (Const x) (Fun zy)  = Fun $ \z -> (x, zy z)
pairS (Fun zx)  (Fun zy)  = Fun $ \z -> (zx z, zy z)

-- | Forgets constness
($?) :: (a -? b) -> a -> b
Const b $? _ = b
Fun f   $? a = f a

infixl 9 $?

-----------------

class Applicative f => Selective f where
  (<*?) :: f (a -? b) -> f a -> f b
  (<*?) = liftS2 id
  
  liftS2 :: (a -> (b -? c)) -> f a -> f b -> f c
  liftS2 f x y = f <$> x <*? y

infixl 4 <*?

select :: (Selective f) => f (Either a b) -> f (a -> b) -> f b
select x y = (f <$> x) <*? y
  where
    f (Left a) = Fun ($ a)
    f (Right b) = Const b

-------------------

data Night f g b =
  forall a. Night (f (a -? b)) (g a)

instance (Functor f) => Functor (Night f g) where
  fmap f (Night fab ga) = Night (fmap (fmap f) fab) ga

hbimapNight :: (forall x. f x -> f' x) -> (forall x. g x -> g' x) ->
              Night f g c -> Night f' g' c
hbimapNight trF trG (Night fab ga) = Night (trF fab) (trG ga)

smapNight :: Functor f => (b -? c) -> Night f g b -> Night f g c
smapNight bc (Night fab ga) = Night ((bc .) <$> fab) ga

-- Is Night associative? No!

nAssocL :: (Functor f) => Night f (Night g h) c -> Night (Night f g) h c
nAssocL (Night fbc (Night gab ha)) =
  Night (Night (compose' <$> fbc) gab) ha
  where
    compose' :: (b -? c) -> (a -? b) -? (a -? c)
    compose' (Const c) = Const (Const c)
    compose' (Fun bc)  = Fun (fmap bc)

nAssocR :: (Functor f, Functor g) => Night (Night f g) h x -> Night f (Night g h) x
nAssocR (Night (Night fabc ga) hb) =
    Night
     (uncurry' <$> fabc)
     (Night (Fun . (,) <$> ga) hb)
       -- both of (ga, hb) have no data to branch const and non-const cases 
  where
    -- uncurry' collapses 2 levels of distinguished constness into 1 level
    uncurry' :: (a -? (b -? c)) -> (a,b) -? c
    uncurry' (Const (Const c)) = Const c
    uncurry' (Const (Fun bc))  = Fun $ \(_,b) -> bc b
    uncurry' (Fun abc)         = Fun $ \(a,b) -> abc a $? b

-- `Night (Night f g) h` exposes /strictly larger information/ about branches than
-- `Night f (Night g h)`. Therefore, there /can not/ be any isomorphism between them!