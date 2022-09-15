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
import Control.Applicative(Applicative(..))

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

(Const d . bc) . ab = Const d . ab = Const d
Const d . (bc . ab) = Const d

(Fun cd . Const c) . ab = Const (cd c)
Fun cd . (Const c . ab) = Fun cd . Const c = Const (cd c)

(Fun cd . Fun bc) . Const b = Const ((cd . bc) b)
Fun cd . (Fun bc . Const b) = Const (cd (bc b))

(Fun cd . Fun bc) . Fun ab = Fun (cd . bc . ab)
Fun cd . (Fun bc . Fun ab) = Fun (cd . bc . ab)

-}

fstS :: (a, b) -? a
fstS = Fun fst

sndS :: (a, b) -? b
sndS = Fun snd

umpProductS :: (z -? x) -> (z -? y) -> z -? (x, y)
umpProductS (Const x) (Const y) = Const (x, y)
umpProductS (Fun zx)  (Const y) = Fun $ \z -> (zx z, y)
umpProductS (Const x) (Fun zy)  = Fun $ \z -> (x, zy z)
umpProductS (Fun zx)  (Fun zy)  = Fun $ \z -> (zx z, zy z)

($?) :: (a -? b) -> a -> b
Const b $? _ = b
Fun f   $? a = f a

infixl 9 $?

-----------------

class Applicative f => Selective f where
  (<*?) :: f (a -? b) -> f a -> f b
  (<*?) = liftS2 id
  
  liftS2 :: (a -? b -? c) -> f a -> f b -> f c
  liftS2 f x y = pure f <*? x <*? y

infixl 4 <*?

select :: (Selective f) => f (Either a b) -> f (a -> b) -> f b
select x y = (f <$> x) <*? y
  where
    f (Left a) = Fun ($ a)
    f (Right b) = Const b

-------------------

{-
data Night f g b =
  forall a. Night (f (a -? b)) (g a)

instance (Functor f) => Functor (Night f g) where
  fmap f (Night fab ga) = Night (fmap (fmap f) fab) ga

hbimapNight :: (forall x. f x -> f' x) -> (forall x. g x -> g' x) ->
              Night f g c -> Night f' g' c
hbimapNight delta eta (Night fab ga) = Night (delta fab) (eta ga)

-- is Night a monoid?

nAssoc1 :: (Functor f) => Night f (Night g h) x -> Night (Night f g) h x
nAssoc1 (Night fbx (Night gab ha)) =
  Night (Night (compose' <$> fbx) gab) ha
  where
    compose' (Const x) = Const (Const x)
    compose' (Fun bx)  = Fun $ \ab -> bx <$> ab

nAssoc2 :: (Functor f, Functor g) => Night (Night f g) h x -> Night f (Night g h) x
nAssoc2 (Night (Night fabx ga) hb) = Night (f <$> fabx) (Night (g <$> ga) hb)
  where
    f (Const (Const x)) = Const x
    f abx               = Fun $ \(a,b) -> abx $? a $? b
       -- Destroying Const-ness!
    
    g a = Fun ((,) a)

-}

data Night f g c =
  forall a b. Night (a -? b -? c) (f a) (g b)

instance Functor (Night f g) where
  fmap f (Night g fa gb) = Night (fmap (fmap f) g) fa gb

nAssoc1 :: Night f (Night g h) x -> Night (Night f g) h x
nAssoc1 (Night alpha fa (Night beta gb hc)) = Night gamma (Night delta fa gb) hc
  where
    -- alpha :: a -? tmp -? x
    -- beta :: b -? c -? tmp

    -- gamma :: (c -? x) -? c -? x
    -- delta :: a -? b -? c -? x

    gamma = id

    delta = case (alpha, beta) of
      (Const tmp_x, Const c_tmp) -> Const $ Const $ tmp_x . c_tmp
      (Const tmp_x, Fun beta')   -> Const $ Fun $ \b -> tmp_x . beta' b
      (Fun alpha',  Const c_tmp) -> Fun $ \a -> Const $ alpha' a . c_tmp
      (Fun alpha',  Fun beta')   -> Fun $ \a -> Fun $ \b -> alpha' a . beta' b

nAssoc2 :: Night (Night f g) h x -> Night f (Night g h) x
nAssoc2 (Night eps (Night zeta fa gb) hc) = Night eta fa (Night theta gb hc)
  where
    -- eps  :: tmp -? c -? x
    -- zeta :: a -? b -? tmp

    -- eta   :: a -? (a -? x) -? x
    -- theta :: b -? c -? a -? x

    eta = Fun $ \a -> Fun ($? a)
      -- requires fa always

    theta = case (eps, zeta) of
      (Const c_x, _)                 -> Const $ Const <$> c_x
      (Fun eps',  Const (Const tmp)) -> Const $ Const <$> eps' tmp
      (Fun eps',  Const (Fun b_tmp)) -> Fun $ \b -> Const <$> eps' (b_tmp b)
      (Fun eps',  Fun zeta') ->
        Fun $ \b -> Fun $ \c -> Fun $ \a -> eps' (zeta' a $? b) $? c
        -- This also requires gb and hc always

{-

nAssoc* is associator

[Isomorphism]
  nAssoc1 . nAssoc2 = id
  nAssoc2 . nAssoc1 = id

[Pentagon Identity]
  nAssoc2 . nAssoc2 = (id ⊗ nAssoc2) . nAssoc2 . (nAssoc2 ⊗ id)

  (⊗) = hbimapNight

  * Both sides of equation has type

    forall x. Night (Night (Night e f) g) h x -> Night e (Night f (Night g h)) x

-}

data FreeS f c where
  Pure :: c -> FreeS f c
  LiftS2 :: (a -? b -? c) -> FreeS f a -> f b -> FreeS f c

instance Functor (FreeS f) where
  fmap f (Pure c) = Pure (f c)
  fmap f (LiftS2 g sa fb) = LiftS2 (fmap (fmap f) g) sa fb

instance Applicative (FreeS f) where
  pure = Pure
  liftA2 = liftA2Default

liftA2Default :: (Selective f) => (a -> b -> c) -> f a -> f b -> f c
liftA2Default f = liftS2 (Fun $ \a -> Fun $ \b -> f a b)

instance Selective (FreeS f) where
  liftS2 f (Pure a) (Pure b) = Pure (f $? a $? b)
  liftS2 f (Pure a) (LiftS2 g sx fy) = LiftS2 (fmap ((f $? a) .) g) sx fy
  liftS2 f (LiftS2 g sx fy) (Pure b) =
    case f of
      Const b_c -> LiftS2 (Const (Const (b_c $? b))) sx fy
      Fun f'    -> let f'' a = f' a $? b
                   in LiftS2 (fmap (fmap f'') g) sx fy
  liftS2 f sa (LiftS2 g sx fy) = LiftS2 id (liftS2 h sa sx) fy
    where
      -- f :: a -? b -? c
      -- g :: x -? y -? b
      -- h :: a -? x -? y -? c
      h = case (f,g) of
        (Const b_c, Const y_b) -> Const $ Const $ b_c . y_b
        (Const b_c, Fun g')    -> Const $ Fun $ \x -> b_c . g' x
        (Fun f',    Const y_b) -> Fun $ \a -> Const $ f' a . y_b
        (Fun f',    Fun g')    -> Fun $ \a -> Fun $ \x -> f' a . g' x
