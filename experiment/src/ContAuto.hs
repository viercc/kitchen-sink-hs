{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
module ContAuto where
import Control.Lens (hasn't)

newtype R = R Int
    deriving (Show, Read, Eq, Ord, Enum, Bounded, Num)

type Cont r a = (a -> r) -> r

data ContMonad r = DictContMonad {
     pure' :: forall a. a -> Cont r a,
     bind' :: forall a b. (a -> Cont r b) -> Cont r a -> Cont r b
  }

{-

Monad laws (in terms of pure' and bind')

bind' pure' = id
        ...... [monad-unit-1]
bind f . pure = f
        ...... [monad-unit-2]
bind' f . bind' g = bind' (bind' f . g)
        ...... [monad-assoc]

-}

-- @Iso a a@ 
data Auto a = Auto (a -> a) (a -> a)

autoToMonad :: Auto r -> ContMonad r
autoToMonad (Auto h h') = DictContMonad {
        pure' = \a k -> h (k a),
        bind' = \f m k -> m (\a -> h' (f a k))
    }

{-

autoToMonad is lawful

Given:
  h . h' = h' . h = id
  pure' a k = h (k a)
  bind' f m k = m (\a -> h' (f a k))
======================
[monad-assoc]
    (bind' f . bind' g) m k
      = bind' f (bind' g m) k
      = bind' f (\j -> m (\a -> h' (g a j))) k
      = (\j -> m (\a -> h' (g a j))) (\b -> h' (f b k))
      = m $ \a -> h' $ g a $ \b -> h' $ f b k
      = m $ \a -> h' (bind' f (g a) k)
      = m $ \a -> h' ((bind' f . g) a k)
      = bind' (bind' f . g) m k
[monad-unit-1]
    bind' pure' m k
      = m $ \a -> h' (pure' a k)
      = m $ \a -> h' (h (k a))
      = m $ \a -> k a
      = m k
[monad-unit-2]
    (bind' f . pure) a k
      = bind' f (pure a) k
      = pure a $ \a -> h' (f a k)
      = h (h' (f a k))
      = f a k

-}

ev :: a -> Cont r a
ev a f = f a

monadToAuto :: ContMonad r -> Auto r
monadToAuto (DictContMonad{..}) = Auto h h'
  where
    h r = pure' () (const r)
    h' r = bind' ev (ev ()) (const r)

{-

monadToAuto . autoToMonad = id :: Auto r

monadToAuto (autoToMonad (Auto h h'))
= monadToAuto (DictContMonad{ pure', bind' })
    where
      pure' a k = h (k a)
      bind' f m k = m (\a -> h' (f a k))
= Auto g g'
    where
      pure' a k = h (k a)
      bind' f m k = m (\a -> h' (f a k))
      g r = pure' () (const r)
          = h (const r ())
          = h r
      g' r = bind' ev (ev ()) (const r)
           = ev () (\a -> h' (ev a (const r)))
           = h' (ev () (const r))
           = h' r
= Auto g g'
    where
      g r = h r
      g' r = h' r
= Auto h h'
-}
