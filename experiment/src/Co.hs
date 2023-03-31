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
import Data.Bifunctor (Bifunctor(..))

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

data Tu f a = Tu {
    _ix :: forall x. f x -> x,
    _val :: f () -> a
  }
  deriving Functor

runTu :: Functor f => Tu f a -> f s -> (s, a)
runTu (Tu ix val) fs = (ix fs, val (void fs))

tupo :: Functor f => Tu f a -> Po f a
tupo tu = Po (runTu tu)

potu :: Po f a -> Tu f a
potu po = Tu (fst . runPo po) (snd . runPo po)

instance Comonad f => Applicative (Tu f) where
    pure a = Tu extract (const a)
    Tu ix f <*> Tu ix' g = Tu (ix =<= ix') (\f1 -> f f1 $ ix (extend g f1))

instance Comonad f => Monad (Tu f) where
    ma >>= k = joinTu $ fmap k ma

joinTu :: Comonad f => Tu f (Tu f a) -> Tu f a
joinTu mma = Tu ix' val'
  where
    ix' fs
      = let ma = _val mma (void fs)
        in _ix mma (extend (_ix ma) fs)
    val' f1
      = let ma = _val mma f1
        in _ix mma (extend (_val ma) f1)

{-
joinTu mma
    = potu $ joinPo $ fmap tupo (tupo mma)
    = potu $ Po $ ev . runPo (fmap tupo (tupo mma)) . extend (flip runPo)
    = potu $ Po $ ev . runPo (tupo mma) . extend (flip (runPo . tupo))
    = potu $ Po $ ev . runTu mma . extend (flip runTu)
    = Tu ix' val'

  where
    ix' = fst . ev . runTu mma . extend (flip runTu)
    ix' fs
      = fst . ev . runTu mma $ extend (flip runTu) fs
      = let fm = extend (flip runTu) fs
        in fst . ev $ runTu mma fm
      = let fmr = extend (flip runTu) fs
        in fst . ev $ (_ix mma fmr, _val mma (void fmr))
      = let fmr = extend (flip runTu) fs
        in fst . ev $ (_ix mma fmr, _val mma (void fs))
      = let ma = _val mma (void fs)
            fmr = extend (flip runTu) fs
        in fst . ev $ (_ix mma fmr, ma)
      = let ma = _val mma (void fs)
            fmr = extend (flip runTu) fs
        in fst $ _ix mma fmr ma
      = let ma = _val mma (void fs)
            fmr' = fmap ($ ma) $ extend (flip runTu) fs
        in fst $ _ix mma fmr'
      = let ma = _val mma (void fs)
            fmr' = extend (runTu ma) fs
        in fst $ _ix mma fmr'
      = let ma = _val mma (void fs)
        in fst $ _ix mma (extend (runTu ma) fs)
      = let ma = _val mma (void fs)
        in _ix mma (extend (fst . runTu ma) fs)
      = let ma = _val mma (void fs)
        in _ix mma (extend (_ix ma) fs)
    
    val' = snd . ev . runTu mma . extend (flip runTu)
    val' f1
      = let ma = _val mma f1
        in _ix mma (extend (_val ma) f1)
-}

-- void (extend f w) = void w
-- void (extend f w)
--  = fmap (const ()) $ extend f w
--  = extend (const () . f) w
--  = extend (const ()) w
--  = extend (extract . fmap ()) w
--  = extend extract (fmap () w)
--  = fmap () w = void w