{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module PartialMonoid(
    -- * PartialMonoid
    PartialMonoid(..),
    Discrete(..),
    DynCategory(..),

    -- * Unicategory
    Level(..),
    Unicategory(..),

) where

import Data.Bifunctor
import Data.PartialSemigroup

import Type.Reflection
import Control.Category
import Prelude hiding ((.), id)
import Control.Applicative (ZipList)
import Data.Void
import Data.Kind
import Control.Monad.Fix (MonadFix)
import Data.Functor.Identity
import Data.Maybe (isJust)

-- | Partial semigroups with identities.
--  
--  An /identity/ is an element @u@ satisfying both of the following properties.
--  
--  - For any element @x@, @u '<>?' x@ is either @Just x@ or @Nothing@.
--  - For any element @x@, @x <>? u@ is either @Just x@ or @Nothing@.
--  
--  A /left/ identity of @x@ is an identity @u@ such that @u <>? x = Just x@.
--  Similarly, a /right/ identity of @x@ is an identity @v@ such that @x <>? v = Just x@.
--  
--  Any value @x@ of a @PartialMonoid@ must have at least one left identity and at least one right identity.
--  The left and right identities of @x@ is not guaranteed to be unique, but an instance should choose one
--  and provide them through 'leftId' and 'rightId' functions.
--  
--  If the partial semigroup has the following /transitive/ property, left and right identities
--  become unique each.
--  
--  - For every combination of elements @x,y,z@, if any two among the following three are true,
--    then the rest is true too.
--
--      - @x <>? y = Just xy@
--      - @y <>? z = Just yz@
--      - @xy <>? z = x <>? yz = Just xyz@
--  
--  A transitive @PartialMonoid@ can be seen as an untyped realization of a 'Category',
--  forgetting distinction between arrows of different types and
--  composition of arrows represented as partial function which fails if and only if
--  the of arrows does not align.
class PartialSemigroup a => PartialMonoid a where
    -- | @leftId x@ is an identity and @leftId x <>? x = Just x@ 
    leftId :: a -> a
    -- | @rightId x@ is an identity and @x <>? rightId x = Just x@ 
    rightId :: a -> a

newtype Discrete a = Discrete { getDiscrete :: a }
  deriving stock (Show, Read, Eq, Ord, Bounded)
  deriving newtype Enum
  deriving (Functor, Applicative, Monad, MonadFix) via Identity

instance Eq a => PartialSemigroup (Discrete a) where
    Discrete a <>? Discrete b
       | a == b = Just (Discrete a)
       | otherwise = Nothing

instance Eq a => PartialMonoid (Discrete a) where
    leftId = id
    rightId = id

instance (PartialMonoid a, PartialMonoid b) => PartialMonoid (Either a b) where
    leftId = bimap leftId leftId
    rightId = bimap rightId rightId

instance (PartialMonoid a, PartialMonoid b) => PartialMonoid (a, b) where
    leftId = bimap leftId leftId
    rightId = bimap rightId rightId

instance (PartialMonoid a, PartialMonoid b, PartialMonoid c) => PartialMonoid (a, b, c) where
    leftId (a,b,c) = (leftId a, leftId b, leftId c)
    rightId (a,b,c) = (rightId a, rightId b, rightId c)

instance Monoid a => PartialMonoid (Total a) where
    leftId _ = Total mempty
    rightId _ = Total mempty

-- | Non-transitive
instance PartialMonoid (AtMostOne a) where
    leftId _ = AtMostOne Nothing
    rightId _ = AtMostOne Nothing

deriving via Total Void
    instance PartialSemigroup Void

instance PartialMonoid Void where
    leftId = absurd
    rightId = absurd

deriving via Total () instance PartialMonoid ()
deriving via Total [a] instance PartialMonoid [a]

instance PartialMonoid a => PartialMonoid (ZipList a) where
    leftId as = leftId <$> as
    rightId as = rightId <$> as

data DynCategory cat where
    DynCategory :: (Typeable a, Typeable b) => cat a b -> DynCategory cat

instance Category cat => PartialSemigroup (DynCategory cat) where
    DynCategory f <>? DynCategory g = case eqTypeRep (domType f) (codType g) of
        Just HRefl -> Just $ DynCategory (f . g)
        Nothing   -> Nothing

domType :: (Typeable a) => p a b -> TypeRep a
domType _ = typeRep

codType :: (Typeable b) => p a b -> TypeRep b
codType _ = typeRep

domId :: Category p => proxy a b -> p a a
domId _ = id

codId :: Category p => proxy a b -> p b b
codId _ = id

instance Category cat => PartialMonoid (DynCategory cat) where
    leftId (DynCategory f) = DynCategory $! codId f
    rightId (DynCategory f) = DynCategory $! domId f

data Level = Z | S Level

class (forall n. PartialMonoid (u ('S n))) => Unicategory u where
    identity :: u n -> u ('S n)
    boundary :: u ('S n) -> (u n, u n)

    -- @identity x@ is an identity (in the PartialMonoid sense)


    -- leftId = identity . fst . boundary
    -- rightId = identity . snd . boundary

    -- boundary . identity = \x -> (x,x)
    -- boundary . fst . boundary = boundary . snd . boundary

    -- boundary f = (x,x') 
    -- boundary g = (y,y')
    -- x <>? y = Just xy
    -- x' <>? y' = Just x'y'
    
    -- | Left whisker
    -- 
    -- > boundary x = (g, g')
    --
    -- @f <>? g = Just fg@ ⇔ @f <>? g' = Just fg'@ ⇔ @f ~~< x = Just fx@
    --
    -- > boundary fx = (fg, fg')
    -- 
    -- > boundary y = (g', g'')
    -- > x <>? y = Just xy
    (~~<) :: u n -> u ('S n) -> Maybe (u ('S n))


data FromCategory k (cat :: k -> k -> Type) (n :: Level) where
    Obj :: TypeRep (a :: k) -> FromCategory k cat 'Z
    Mor :: TypeRep (a :: k) -> TypeRep (b :: k) -> cat a b -> FromCategory k cat ('S 'Z)
    Trunc :: FromCategory k cat ('S n) -> FromCategory k cat ('S ('S n))

instance (forall a b. Eq (cat a b), Category cat) => Unicategory (FromCategory k cat) where
    identity (Obj ty) = Mor ty ty id
    identity v@Mor{} = Trunc v
    identity v@Trunc{} = Trunc v

    boundary (Mor tyA tyB _) = (Obj tyA, Obj tyB)
    boundary (Trunc f) = (f, f)

instance (forall a b. Eq (cat a b)) => Eq (FromCategory k cat n) where
    Obj tyA == Obj tyB = isJust $ eqTypeRep tyA tyB
    Mor tyA tyB f == Mor tyA' tyB' g = case (eqTypeRep tyA tyA', eqTypeRep tyB tyB') of
        (Just HRefl, Just HRefl) -> f == g
        _                        -> False
    Trunc f == Trunc g = f == g

instance (forall a b. Eq (cat a b), Category cat) => PartialSemigroup (FromCategory k cat n) where
    Mor b c f <>? Mor a b' g = case eqTypeRep b b' of
        Just HRefl -> Just $ Mor a c (f . g)
        Nothing    -> Nothing
    x <>? y | x == y    = Just x
            | otherwise = Nothing

instance (forall a b. Eq (cat a b), Category cat) => PartialMonoid (FromCategory k cat n) where
    leftId (Mor _ tyB _) = Mor tyB tyB id
    leftId x             = x

    rightId (Mor tyA _ _) = Mor tyA tyA id
    rightId x             = x