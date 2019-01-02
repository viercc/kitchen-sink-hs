{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
module AdHocInstances(
  Group(..),
  GroupExpr(),
  inj,
  adhocGroup
) where

import           Data.Semigroup

import           Data.Proxy
import           Data.Reflection

import           Data.Coerce

class (Semigroup a, Monoid a) => Group a where
  inv :: a -> a
  
  gtimes :: (Integral b) => b -> a -> a
  gtimes b a
    | b <  0    = inv (stimes (negate b) a)
    | b == 0    = mempty
    | otherwise = stimes b a

--------------------------------------------------

newtype GroupExpr a =
  GroupExpr { runGroup :: forall r. (Coercible a r, Group r) => r }

inj :: a -> GroupExpr a
inj a = GroupExpr $ coerce a

instance Semigroup (GroupExpr a) where
  GroupExpr ma <> GroupExpr mb = GroupExpr $ ma <> mb
  stimes n (GroupExpr ma) = GroupExpr $ stimes n ma

instance Monoid (GroupExpr a) where
  mempty = GroupExpr mempty
  mappend = (<>)

instance Group (GroupExpr a) where
  inv (GroupExpr ma) = GroupExpr $ inv ma
  gtimes n (GroupExpr ma) = GroupExpr $ gtimes n ma

----------------------------------------------------

newtype AdHocGroup s a = AsGroup { forgetGroup :: a }
  deriving (Eq, Ord)

data GroupOp a =
  GroupOp { groupUnit   :: a
          , groupAppend :: a -> a -> a
          , groupInv    :: a -> a
          , groupTimes  :: forall b. Integral b => b -> a -> a
          }

groupOp :: a -> (a -> a -> a) -> (a -> a) -> GroupOp a
groupOp unit append inv' = GroupOp unit append inv' gtimes'
  where
    gtimes' b a
      | b <  0    = inv' (stimes' (negate b) a)
      | b == 0    = unit
      | otherwise = stimes' b a

    stimes' n a = loop unit a n
    loop accum a n
      | n == 0    = accum
      | even n    = loop accum (a `append` a) (n `quot` 2)
      | otherwise = loop (accum `append` a) (a `append` a) (n `quot` 2)

instance (Reifies s (GroupOp a)) => Semigroup (AdHocGroup s a) where
  AsGroup a <> AsGroup b = AsGroup $ groupAppend (reflect (Proxy :: Proxy s)) a b
  stimes = gtimes

instance (Reifies s (GroupOp a)) => Monoid (AdHocGroup s a) where
  mempty = AsGroup $ groupUnit (reflect (Proxy :: Proxy s))
  mappend = (<>)

instance (Reifies s (GroupOp a)) => Group (AdHocGroup s a) where
  inv (AsGroup a) = AsGroup $ groupInv (reflect (Proxy :: Proxy s)) a
  gtimes n (AsGroup a) = AsGroup $ groupTimes (reflect (Proxy :: Proxy s)) n a

using :: AdHocGroup s a -> Proxy s -> AdHocGroup s a
using = const

adhocGroup :: a -> (a -> a -> a) -> (a -> a) ->
  GroupExpr a ->
  a
adhocGroup unit append inv' expr =
  reify (groupOp unit append inv') $ \p ->
    forgetGroup (runGroup expr `using` p)

--------------------------------------

example1 :: Int
example1 = adhocGroup 0 (+) negate $
  inj 1 <> inv (inj 2) <> mempty

example2 :: Rational -> Rational
example2 x = adhocGroup 1 (*) recip $
  inj x <> inv (inj x <> inj 2)

example3 :: Bool -> Bool -> Bool
example3 x y = adhocGroup False xor id $
  inj x <> inv (inj y) <> inv (inj x)
  where xor = (/=)
