{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MagicHash #-}
module Data.Functor.Derivative where

import Data.Functor.Identity

import Data.Kind
import GHC.Generics
import Data.Coerce

absurdV1 :: V1 a -> b
absurdV1 v1 = case v1 of { }

infixr 9 #.
(#.) :: (Coercible b c) => (b `arr` c) -> (a -> b) -> (a -> c)
_ #. f = coerce f

infixr 9 .#
(.#) :: (Coercible a b) => (b -> c) -> (a `arr` b) -> (a -> c)
f .# _ = coerce f

-- | A class which `Fix f` have a zipper
class (Functor (Der f), Traversable f) => Tooth f where
    type Der f :: Type -> Type
    
    children :: f a -> f (Der f a, a)
    children = runIdentity #. traverseChildren (curry Identity)

    traverseChildren :: Applicative g => (Der f a -> a -> g b) -> f a -> g (f b)
    traverseChildren h = traverse (uncurry h) . children

    parent :: Der f a -> a -> f a

instance Tooth V1 where
    type Der V1 = V1
    children = absurdV1
    parent = absurdV1

instance Tooth U1 where
    type Der U1 = V1
    children _ = U1
    parent = absurdV1

instance Tooth (K1 i c) where
    type Der (K1 i c) = V1
    children (K1 c) = K1 c
    parent = absurdV1

instance Tooth f => Tooth (M1 p i f) where
    type Der (M1 p i f) = Der f
    children = M1 #. children .# unM1
    parent df a = M1 (parent df a)

instance Tooth f => Tooth (Rec1 f) where
    type Der (Rec1 f) = Der f
    children = Rec1 #. children .# unRec1
    parent df a = Rec1 (parent df a)

instance Tooth Par1 where
    type Der Par1 = U1
    children (Par1 a) = Par1 (U1, a)
    parent _ a = Par1 a

instance (Tooth f, Tooth g) => Tooth (f :+: g) where
    type Der (f :+: g) = Der f :+: Der g
    traverseChildren h (L1 fa) = L1 <$> traverseChildren (h . L1) fa
    traverseChildren h (R1 ga) = R1 <$> traverseChildren (h . R1) ga

    parent (L1 df) a = L1 (parent df a)
    parent (R1 dg) a = R1 (parent dg a)

instance (Tooth f, Tooth g) => Tooth (f :*: g) where
    type Der (f :*: g) = (Der f :*: g) :+: (f :*: Der g)
    traverseChildren h (f :*: g) =
        (:*:) <$> traverseChildren (\df -> h (L1 (df :*: g))) f
              <*> traverseChildren (\dg -> h (R1 (f :*: dg))) g

    parent (L1 (df :*: g)) a = parent df a :*: g
    parent (R1 (f :*: dg)) a = f :*: parent dg a

instance (Tooth f, Tooth g) => Tooth (f :.: g) where
    type Der (f :.: g) = (Der f :.: g) :*: Der g
    traverseChildren h (Comp1 fg) = Comp1 <$>
        traverseChildren (\dfg g -> traverseChildren (\dg -> h (Comp1 dfg :*: dg)) g) fg
    
    parent (Comp1 dfg :*: dg) a = Comp1 (parent dfg (parent dg a))
