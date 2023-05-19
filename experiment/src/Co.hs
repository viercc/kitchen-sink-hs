{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
module Co where

import Control.Monad
import Control.Comonad

newtype Co f a = Co { runCo :: forall r. f (a -> r) -> r }

instance Functor f => Functor (Co f) where
    fmap g (Co c) = Co (c . fmap (. g))

instance Comonad f => Applicative (Co f) where
    pure a = Co \far -> extract far a
    (<*>) = ap

instance Comonad f => Monad (Co f) where
    ma >>= k = joinCo $ fmap k ma

joinCo :: Comonad f => Co f (Co f a) -> Co f a
joinCo mma = Co $ runCo mma . extend (flip runCo)

newtype Po f a = Po { runPo :: forall s. f s -> (s, a) }
  deriving Functor

ev :: (a -> b, a) -> b
ev (f, a) = f a

poco :: Po f a -> Co f a
poco (Po p) = Co (ev . p)

copo :: Functor f => Co f a -> Po f a
copo (Co c) = Po (c . fmap (,))

instance Comonad f => Applicative (Po f) where
    pure a = Po \fs -> (extract fs, a)
    wa <*> wb = Po \fs -> case runPo wa $ extend (runPo wb) fs of
        ((s,b),a) -> (s, a b)

instance Comonad f => Monad (Po f) where
    (>>=) :: Comonad f => Po f a -> (a -> Po f b) -> Po f b
    ma >>= k = joinPo $ fmap k ma

joinPo :: Comonad f => Po f (Po f a) -> Po f a
joinPo mma = Po $ ev . runPo mma . extend (flip runPo)

{-
joinPo mma
    = copo $ joinCo $ fmap poco (poco mma)
    = copo $ Co $ runCo (fmap poco (poco mma)) . extend (flip runCo)
    = Po $ runCo (poco mma) . extend (flip (runCo . poco)) . fmap (,)
    = Po $ ev . runPo mma . extend (\fz ma -> ev (runPo ma fz)) . fmap (,)
    = Po $ ev . runPo mma . extend (\fz ma -> ev (runPo ma (fmap (,) fz)))
    = Po $ ev . runPo mma . extend (\fz ma -> ev (first (,) (runPo ma fz)))
    = Po $ ev . runPo mma . extend (\fz ma -> (runPo ma fz))
    = Po $ ev . runPo mma . extend (flip runPo)
-}

newtype Move f = Move { appMove :: forall x. f x -> x }
type Key f = f ()

instance Comonad f => Semigroup (Move f) where
  Move f <> Move g = Move (f =>= g)
  --               = Move (g . extend f)
  --               = Move (g . fmap f . duplicate)
  --               = Move (f . g . duplicate)

instance Comonad f => Monoid (Move f) where
  mempty = Move extract

actMove :: Comonad f => Move f -> f a -> f a
actMove (Move f) k = f (duplicate k)

{-

@actMove@ is a left monoid action of @Move f@

actMove mempty k
  = extract (duplicate k)
  = k

actMove (Move f) $ actMove (Move g) k
  = actMove (Move f) $ g (duplicate k)
  = f . duplicate . g . duplicate $ k
  = f . g . fmap duplicate . duplicate $ k
  = f . g . duplicate . duplicate $ k
  = (f =>= g) . duplicate $ k
  = actMove (Move (f =>= g)) k
  = actMove (Move f <> Move g) k

-}

data Tu f a = Tu {
    _move :: Move f,
    _val :: Key f -> a
  }
  deriving Functor

runTu :: Functor f => Tu f a -> f s -> (s, a)
runTu (Tu m val) fs = (appMove m fs, val (void fs))

tupo :: Functor f => Tu f a -> Po f a
tupo tu = Po (runTu tu)

potu :: Po f a -> Tu f a
potu po = Tu (Move (fst . runPo po)) (snd . runPo po)

instance Comonad f => Applicative (Tu f) where
    pure a = Tu mempty (const a)
    Tu m1 f <*> Tu m2 g = Tu (m2 <> m1) (\k -> f k $ g (actMove m1 k))

instance Comonad f => Monad (Tu f) where
    ma >>= k = joinTu $ fmap k ma

joinTu :: Comonad f => Tu f (Tu f a) -> Tu f a
joinTu Tu{ _move = m1, _val = f } = Tu m' val'
  where
    m' = Move $ \fs ->
      appMove (_move (f (void fs)) <> m1) fs
    val' k = _val (f k) (actMove m1 k)

{-
joinTu :: Comonad f => Tu f (Tu f a) -> Tu f a
joinTu = potu . joinPo $ fmap tupo (tupo mma)
 = potu . Po . runPo . joinPo $ fmap tupo (tupo mma)
 --            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 = potu . Po . joinAux

joinAux :: Comonad f => Tu f (Tu f a) -> f s -> (s, a)
joinAux mma = runPo . joinPo $ fmap tupo (tupo mma)
  = ev . run
  = ev . runPo (fmap tupo (tupo mma)) . extend (flip runPo)
  = ev . runPo (tupo mma) . extend (flip (runPo . tupo))
  = ev . runTu mma . extend (flip runTu)
joinAux mma fs
  = ev . runTu mma . extend (flip runTu) $ fs
  = ev $ runTu mma fmr
      where
        fmr = extend (flip runTu) fs
  = ev (appMove (_move mma) fmr, _val mma (void fmr))
  = ev (appMove m1 fmr, ma)
      where
        m1 = _move mma
        f = _val mma
        k = void fmr
          = void (extend (flip runTu) fs)
          = void fs
        ma = f k
  = appMove m1 fmr ma
  = ($ ma) $ appMove m1 fmr ma
  -- Naturality of appMove
  = appMove m1 (fmap ($ ma) fmr)
  = appMove m1 fs'
      where
        fs' = fmap ($ ma) fmr
         = fmap ($ ma) $ extend (flip runTu) fs
         = extend (($ ma) . flip runTu) fs
         = extend (runTu ma) fs

joinTu mma@Tu{ _move=m1, _val=f } = Tu (Move m') val'
  where
    m' fs
      = fst $ appMove m1 fs'
          where
            fs' = extend (runTu ma) fs
            ma = f (void fs)
      = appMove m1 fs''
          where
            fs'' = fmap fst fs'
              = fmap fst (extend (runTu ma) fs)
              = extend (fst . runTu ma) fs
              = extend (appMove (_move ma)) fs
      = appMove m1 . extend (appMove (_move ma)) $ fs
      = (appMove (_move ma) =>= appMove m1) $ fs
      = appMove (_move ma <> m1) $ fs
      = appMove (_move (f (void fs)) <> m1) $ fs
    val' k
      = snd $ appMove m1 fs'
      = appMove m1 fs''
          where
            fs'' = fmap snd fs'
              = fmap snd (extend (runTu ma) k)
              = extend (snd . runTu ma) k
              = extend (_val ma) k
      = appMove m1 $ extend (_val ma) k
      = appMove m1 . fmap (_val ma) . duplicate $ k
      = _val ma $ appMove m1 . duplicate $ k
      = _val ma $ actMove m1 k
      = _val (f (void k)) (actMove m1 k)
      = _val (f k) (actMove m1 k)

-}

-- void (extend f w) = void w
-- void (extend f w)
--  = fmap (const ()) $ extend f w
--  = extend (const () . f) w
--  = extend (const ()) w
--  = extend (extract . fmap ()) w
--  = extend extract (fmap () w)
--  = fmap () w = void w