{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Control.Applicative.Trans.FreeAp(
    ApT(..),

    ViewApT, viewApT, fromViewApT,

    hoistApT, transApT,
    liftF, liftT, appendApT,
    
    iterT, foldApT, 
    fjoinApTLeft, fjoinApTRight
) where

import Data.Functor.Day ( Day(..) )
import Control.Applicative.Lift ( Lift(..) )
import Data.Function ((&))
import Control.Applicative

import Data.Functor.Flip1
import FFunctor ( FFunctor(..) )
import FMonad ( FMonad(..) )

-- | > ApT f g ~ g + (g ⊗ f ⊗ 'ApT' f g)
--
-- - @f + g@ means @'Data.Functor.Sum' f g@
-- - @f ⊗ g@ means @'Day' f g@
data ApT f g x =
      PureT (g x)
    | forall a b c. ApT (g a) (f b) (ApT f g c) (a -> b -> c -> x)

-- | > 'ViewApT' f g ~ g ⊗ 'Lift' (f ⊗ 'ApT' f g)
type ViewApT f g = Day g (Lift (Day f (ApT f g)))

viewApT :: ApT f g x -> ViewApT f g x
viewApT (PureT gx) = Day gx (Pure ()) const
viewApT (ApT ga fb rc x) = Day ga (Other (Day fb rc (\b c a -> x a b c))) (&)

fromViewApT :: Functor g => ViewApT f g x -> ApT f g x
fromViewApT (Day ga lifted g) = case lifted of
    Pure b -> PureT $ (`g` b) <$> ga
    Other (Day fb rc h) -> ApT ga fb rc (\a b c -> g a (h b c))

instance Functor g => Functor (ApT f g) where
    fmap h (PureT gx) = PureT $ fmap h gx
    fmap h (ApT ga fb rc x) = ApT ga fb rc (\a b c -> h (x a b c))
    
    x <$ PureT gx = PureT (x <$ gx)
    x <$ ApT ga fb rc _ = ApT ga fb rc (\_ _ _ -> x)

instance Applicative g => Applicative (ApT f g) where
    pure = PureT . pure
    PureT gx <*> PureT gy = PureT (gx <*> gy)
    PureT gx <*> ApT ga fb rc y = ApT (liftA2 (\x a b c -> x (y a b c)) gx ga) fb rc id
    ApT ga fb rc x <*> rest = ApT ga fb (liftA2 (\c y a b -> x a b c y) rc rest) (\a b k -> k a b)

    PureT gx *> PureT gy = PureT (gx *> gy)
    PureT gx *> ApT ga fb rc y = ApT (gx *> ga) fb rc y
    ApT ga fb rc _ *> rest = ApT ga fb (rc *> rest) (\_ _ y -> y)

    PureT gx <* PureT gy = PureT (gx <* gy)
    PureT gx <* ApT ga fb rc _ = ApT (gx <* ga) fb rc (\x _ _ -> x)
    ApT ga fb rc x <* rest = ApT ga fb (rc <* rest) x

-- | Lift an applicative homomorphism between @g,h@ to
--   an applicative homomorphism between @ApT f g, ApT f h@
hoistApT :: (forall a. g a -> h a) -> ApT f g b -> ApT f h b
hoistApT g2h (PureT gx) = PureT (g2h gx)
hoistApT g2h (ApT ga fb rc x) = ApT (g2h ga) fb (hoistApT g2h rc) x

-- | Lift any natural transfomation between @f,g@ to
--   an applicative homomorphism between @ApT f h, ApT g h@
transApT :: (forall a. f a -> g a) -> ApT f h b -> ApT g h b
transApT _ (PureT gx) = PureT gx
transApT f2g (ApT ga fb rc x) = ApT ga (f2g fb) (transApT f2g rc) x

-- | Lift an applicative action @g x@ to @ApT f g x@
liftT :: g x -> ApT f g x
liftT = PureT

-- | Lift an uninterpreted action @f x@ to @ApT f g x@
liftF :: Applicative g => f x -> ApT f g x
liftF fx = ApT (pure ()) fx (pure ()) (\_ x _ -> x)

appendApT :: ApT f g a -> f b -> ApT f g c -> (a -> b -> c -> x) -> ApT f g x
appendApT prefix fb postfix x = case prefix of
    PureT ga -> ApT ga fb postfix x
    ApT ga' fb' prefix' a -> ApT ga' fb' (appendApT prefix' fb postfix (,,)) (\a' b' ~(c',b,c) -> x (a a' b' c') b c)

iterT :: forall f g x. Applicative g => (forall a b c. (a -> b -> c) -> f a -> g b -> g c) -> ApT f g x -> g x
iterT op = go
  where
    go :: forall y. ApT f g y -> g y 
    go (PureT gx) = gx
    go (ApT ga fb rc x) = liftA2 (\a k -> k a) ga (op (\b c a -> x a b c) fb (go rc))

foldApT :: forall f g h x. Applicative h => (forall a. f a -> h a) -> (forall a. g a -> h a) -> ApT f g x -> h x
foldApT f2h g2h = go
  where
    go :: forall y. ApT f g y -> h y
    go (PureT gx) = g2h gx
    go (ApT ga fb rc x) = liftA3 x (g2h ga) (f2h fb) (go rc)

fjoinApTLeft :: forall f g x. ApT f (ApT f g) x -> ApT f g x
fjoinApTLeft = go
  where
    go :: forall y. ApT f (ApT f g) y -> ApT f g y
    go (PureT inner) = inner
    go (ApT inner fb rest y) = appendApT inner fb (go rest) y

fjoinApTRight :: Applicative g => ApT (ApT f g) g x -> ApT f g x
fjoinApTRight = foldApT id liftT

instance FFunctor (ApT f) where
    ffmap = hoistApT

instance Functor g => FFunctor (Flip1 ApT g) where
    ffmap f2g = Flip1 . transApT f2g . unFlip1

instance Applicative g => FMonad (Flip1 ApT g) where
    fpure = Flip1 . liftF
    fjoin = Flip1 . foldApT unFlip1 liftT . unFlip1