{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-

https://x.com/ymdfield/status/1961962801574084680

-}
module IxEither where

import Data.Kind (Type)
import Data.Coerce
import Data.Type.Coercion

----------------------------------
-- Using GADT
----------------------------------
type IxEither :: Bool -> Type -> Type -> Type
data IxEither i a b where
  IxLeft :: a -> IxEither False a b
  IxRight :: b -> IxEither True a b

type role IxEither nominal representational representational

-- Having @representational@ role mean you can lift coercibility relation
rep_rep :: (Coercion a a', Coercion b b') -> Coercion (IxEither i a b) (IxEither i a' b')
rep_rep (Coercion, Coercion) = Coercion

-- ... and /unlift/ it too!
un_rep_rep :: Coercion (IxEither i a b) (IxEither i a' b') -> (Coercion a a', Coercion b b')
un_rep_rep Coercion = (Coercion, Coercion)

-- If we have @coercionOnFalse@ ...
coercionOnFalse :: Coercion (IxEither False a b) (IxEither False a b')
coercionOnFalse = undefined

-- ... then we can extract @Coercion b b'@ out of thin air!
badCoercion :: forall (a :: Type) (b :: Type) (b' :: Type). (Coercion a a, Coercion b b')
badCoercion = un_rep_rep coercionOnFalse

----------------------------------
-- Using data family
----------------------------------

data family IxEitherF (i :: Bool) :: Type -> Type -> Type
newtype instance IxEitherF False a b = IxLeft' a
newtype instance IxEitherF True a b = IxRight' b

-- While we /can't/ have representational role on
-- IxEitherF, we can at least /lift/ the coercibility relation!

rep_rep_F :: SBool i -> (Coercion a a', Coercion b b') -> Coercion (IxEitherF i a b) (IxEitherF i a' b')
rep_rep_F SFalse (Coercion, _) = Coercion
rep_rep_F STrue  (_, Coercion) = Coercion

coercionOnFalseF :: Coercion (IxEitherF False a b) (IxEitherF False a b')
coercionOnFalseF = Coercion

----------------------------------

data SBool (i :: Bool) where
  SFalse :: SBool False
  STrue :: SBool True