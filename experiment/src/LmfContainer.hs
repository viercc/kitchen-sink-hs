{-# LANGUAGE PolyKinds, DataKinds, GADTs, TypeFamilies, TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
module LmfContainer where

import Data.Kind (Type)
import Data.Type.Equality
import Data.Proxy

-- * Decidable propositions
data Dec p = Yes p | No (forall a. p -> a)

decToBool :: Dec p -> Bool
decToBool (Yes _) = True
decToBool (No _) = False

dand :: Dec p -> Dec q -> Dec (p,q)
dand (Yes p) (Yes q)   = Yes (p,q)
dand (Yes _) (No notq) = No (\(_,q) -> notq q)
dand (No notp) _       = No (\(p,_) -> notp p)

-- * Singleton type and type-level Semigroup and Monoid
type family Sing (k :: Type) :: k -> Type

class TEq k where
    teq :: Sing k a -> Sing k b -> Dec (a :~: b)

class TSemigroup k where
    type (<>) (a :: k) (b :: k) :: k
    tm :: Sing k a -> Sing k b -> Sing k (a <> b)
    propAssoc :: Sing k a -> Sing k b -> Sing k c -> (a <> b) <> c :~: a <> (b <> c)

class (TSemigroup k) => TMonoid k where
    type MonUnit :: k
    monUnit :: Sing k MonUnit

    propUnitL :: Sing k a -> MonUnit <> a :~: a
    propUnitR :: Sing k a -> a <> MonUnit :~: a

-- | @Some s@ is a type for values of @Sing s a@ for /any/ @a@.
data Some s where
    Some :: Sing s a -> Some s

instance TEq s => Eq (Some s) where
    Some a == Some b = decToBool $ teq a b

instance TSemigroup s => Semigroup (Some s) where
    Some a <> Some b = Some (tm a b)

instance TMonoid s => Monoid (Some s) where
    mempty = Some monUnit

-- | Realization of a container as Functor
data Cont (s :: Type) (p :: s -> Type) a where
    MkCont :: Sing s i -> (p i -> a) -> Cont s p a

instance Functor (Cont s p) where
    fmap f (MkCont i v) = MkCont i (f . v)

-- | @castWith' eq = castWith (sym eq)@
castWith' :: a :~: b -> b -> a
castWith' eq = castWith (sym eq)

-- | Monoidal container.
--
--   /Laws/: Ignoring casting around propositional type equalities
--   regarding TSemigroup/TMonoid laws, these two equations must hold.
--
--   @
--   midFactor monUnit j monUnit = id
--   midFactor i j k . midFactor i' ((i <> j) <> k) k' = midFactor (i' <> i) j (k <> k')
--   @
class TMonoid s => LmfContainer (s :: Type) (p :: s -> Type) where
    {-# MINIMAL (leftFactor, rightFactor) | midFactor #-}
    rightFactor :: Sing s i -> Sing s j -> p (i <> j) -> p j
    rightFactor i j =  midFactor i j monUnit . castWith' (apply Refl (propUnitR (tm i j)))

    leftFactor :: Sing s i -> Sing s j -> p (i <> j) -> p i
    leftFactor i j = midFactor monUnit i j . castWith' (apply Refl (propAssoc monUnit i j `trans` propUnitL (tm i j)))

    midFactor :: Sing s i -> Sing s j -> Sing s k -> p ((i <> j) <> k) -> p j
    midFactor i j k = rightFactor i j . leftFactor (tm i j) k

instance LmfContainer s p => Applicative (Cont s p) where
    pure a = MkCont monUnit (const a)
    MkCont i xs <*> MkCont j ys = MkCont (tm i j) (\p -> xs (leftFactor i j p) $ ys (rightFactor i j p))

--------

instance (TMonoid s) => LmfContainer s Proxy where
    midFactor _ _ _ _ = Proxy

writerToCont :: (Some s, a) -> Cont s Proxy a
writerToCont (Some i, a) = MkCont i (\_proxy -> a)

contToWriter :: Cont s Proxy a -> (Some s, a)
contToWriter (MkCont i v) = (Some i, v Proxy)

-- Example

data SBool (b :: Bool) where
    STrue :: SBool True
    SFalse :: SBool False

type instance Sing Bool = SBool

instance TestEquality SBool where
    testEquality STrue STrue = Just Refl
    testEquality SFalse SFalse = Just Refl
    testEquality _ _ = Nothing

-- | @All@-like behavior i.e. @(<>) = (&&)@
instance TSemigroup Bool where
    type (<>) True b = b
    type (<>) False _ = False
    tm STrue b = b
    tm SFalse _ = SFalse
    propAssoc STrue STrue _ = Refl
    propAssoc STrue SFalse _ = Refl
    propAssoc SFalse _ _ = Refl

instance TMonoid Bool where
    type MonUnit = True
    monUnit = STrue
    propUnitL _ = Refl
    propUnitR STrue = Refl
    propUnitR SFalse = Refl

data MaybeP (b :: Bool) where
    JustP :: MaybeP True

nothingP :: MaybeP False -> a
nothingP p = case p of { }

maybeToCont :: Maybe a -> Cont Bool MaybeP a
maybeToCont Nothing = MkCont SFalse nothingP
maybeToCont (Just a) = MkCont STrue (const a)

contToMaybe :: Cont Bool MaybeP a -> Maybe a
contToMaybe (MkCont i v) = case i of
    SFalse -> Nothing
    STrue  -> Just (v JustP)

instance LmfContainer Bool MaybeP where
    midFactor SFalse _      _      = nothingP
    midFactor STrue  SFalse _      = nothingP
    midFactor STrue  STrue  SFalse = nothingP
    midFactor STrue  STrue  STrue  = id
