{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Monad
import Control.Applicative

newtype Compose f g a = Compose { getCompose :: f (g a) }
  deriving (Show, Eq, Functor)

instance (Applicative f, Applicative g) => Applicative (Compose f g) where
  pure a = Compose $ pure (pure a)
  Compose fgx <*> Compose fgy = Compose $ liftA2 (<*>) fgx fgy

returnC :: forall f g a. (Monad f, Monad g) => a -> f (g a)
returnC = return . return

joinC :: forall f g a. (Monad f, Monad g, Traversable g) =>
                       f (g (f (g a))) -> f (g a)
joinC = (fmap join :: f (g (g a)) -> f (g a) ) .
        (join :: f (f (g (g a))) -> f (g (g a)) ) .
        (fmap sequenceA :: f (g (f (g a))) -> f (f (g (g a))) )

-- | F a ~ Writer (Sum Int) a
data F a = F !Int a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative F where
  pure = return
  (<*>) = ap

instance Monad F where
  return = F 0
  F m a >>= k = case k a of
    F n b -> F (m+n) b

-- | G a ~ Bool -> a
data G a = G a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative G where
  pure = return
  (<*>) = ap

instance Monad G where
  return a = G a a
  G a1 a2 >>= k =
    let G b1 _ = k a1
        G _ b2 = k a2
    in G b1 b2

test :: F (G ())
test = F 1 (return ())

test' :: F (G ())
test' = joinC (returnC test)
