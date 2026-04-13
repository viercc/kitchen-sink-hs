{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Hopf where

import Data.Group
import Control.Comonad
import Data.Functor.Day
import Data.Functor.Day.Comonoid
import Data.Functor.Classes
import Data.Foldable (Foldable(..))
import Data.Functor (void)

-- | Bimonoid of functors
--
-- ===== Laws
--
-- - @extract@ is an applicative morphism in the following sense:
--
--     - @extract (pure a) === a@
--
--         - This law follows from the parametricity:
--           /any/ definable function with type @forall a. a -> a@ must be the 
--           identity function.
--
--     - @extract (x '<*>' y) === extract x (extract y)@
--
-- - @coapply@ is an applicative morphism
--
--     - @coapply (pure a) === pure a = Day (pure ()) (pure ()) (\_ _ -> a)@
--
--         - This law follows from the @Comonoid@ law and the parametricity.
--           
--           From naturalities of @coapply@ and @pure@ which are consequences of the parametricity,
--           @coapply (pure a) = a <$ (coapply (pure ()))$.
--           Then @coapply (pure ()) = Day (pure ()) (pure ()) (\_ _ -> ())@ is a consequence of the @Comonoid@ law.
--
--     - @coapply (x '<*>' y) === coapply x '<*>' coapply y@
--
--         - Note that the right hand side of this equation uses
--           the @Applicative@ instance of 'Day'
--
--           @
--           instance (Applicative f, Applicative g) => Applicative (Day f g)
--           @
--
--           which combines @Day (Day f g) (Day f g)@ to @Day f g@ by
--           first reordering it to @Day (Day f f) (Day g g)@ and combine each component.
class (Applicative f, Comonoid f) => Bimonoid f where
  -- Bimonoid needs no methods

-- | Hopf monoid of functors
--
-- ===== Laws
--
-- @antipode@ is the "inverse" of '<*>'.
--
-- @
-- dap . trans1 antipode . coapply === pure . extract === dap . trans2 antipode . coapply
-- @
class Bimonoid f => Hopf f where
  antipode :: f a -> f a

instance Monoid m => Bimonoid ((,) m)
instance (Group g) => Hopf ((,) g) where
  antipode :: (g, a) -> (g, a)
  antipode (g1, x) = (invert g1, x)

instance Monoid m => Bimonoid ((->) m)
instance (Group g) => Hopf ((->) g) where
  antipode :: (g -> a) -> (g -> a)
  antipode x = x . invert

xor :: Bool -> Bool -> Bool
xor = (/=)

-- * Example

liftEqDefault :: (Traversable t, Eq (t ())) => (a -> b -> Bool) -> t a -> t b -> Bool
liftEqDefault eq ta tb = void ta == void tb && all (uncurry eq) (zip (toList ta) (toList tb))

data V3 a = V3 a a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Eq1 V3 where
  liftEq eq (V3 x1 x2 x3) (V3 y1 y2 y3) = eq x1 y1 && eq x2 y2 && eq x3 y3

instance Applicative V3 where
  pure x = V3 x x x
  V3 x0 x1 x2 <*> V3 y0 y1 y2 = V3 (x0 y0) (x1 y1) (x2 y2)

instance Comonad V3 where
  extract (V3 x0 _ _) = x0
  duplicate = duplicateDefault

instance Comonoid V3 where
  coapply (V3 x0 x1 x2) = Day ix ix $ \i j ->
    case (i + j) `mod` 3 of
      0 -> x0
      1 -> x1
      _ -> x2
    where
      ix = V3 0 1 2 :: V3 Integer

instance Bimonoid V3

instance Hopf V3 where
  antipode (V3 x0 x1 x2) = V3 x0 x2 x1

-- | Twist: Hopf with "non-trivial" antipode
data Twist a b = Twist !Bool (a -> b)
  deriving (Functor)

instance Num a => Applicative (Twist a) where
  pure x = Twist False (pure x)
  Twist s1 f1 <*> Twist s2 f2 = Twist (s1 `xor` s2) (\a -> f1 a (f2 (a `act` s1)))
    where
      act a s = if s then negate a else a

instance Num a => Comonad (Twist a) where
  extract (Twist _ f) = f 0
  duplicate = duplicateDefault

instance Num a => Comonoid (Twist a) where
  coapply (Twist s f) = Day (Twist s id) (Twist s id) (\a1 a2 -> f (a1 + a2))

instance Num a => Bimonoid (Twist a)

instance Num a => Hopf (Twist a) where
  antipode (Twist s f) = Twist s (\a -> f (a `antiact` s))
    where
      -- The inverse for the (Bool, xor) group === id

      -- antiact a s
      --   = negate (a `act` inverse s)
      --   = negate (a `act` s)
      --   = negate (if s then negate a else a)
      --   = if s then a else negate a
      antiact a s0 = if s0 then a else negate a

-- | Isomorphic to @Twist (Z 3) a@
data Twist3 a = Twist3 !Bool (V3 a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Eq1 Twist3 where
  liftEq eq (Twist3 b xs) (Twist3 b' xs') = b == b' && liftEq eq xs xs'

instance Applicative Twist3 where
  pure x = Twist3 False (pure x)
  Twist3 a xs <*> Twist3 b ys = Twist3 (a `xor` b) (xs <*> act a ys)
    where
      act :: Bool -> V3 a -> V3 a
      act c = if c then antipode else id

instance Comonad Twist3 where
  extract (Twist3 _ xs) = extract xs
  duplicate = duplicateDefault

instance Comonoid Twist3 where
  coapply (Twist3 b xs) = case coapply xs of
    Day ixes ixes' op -> Day (Twist3 b ixes) (Twist3 b ixes') op

instance Bimonoid Twist3

instance Hopf Twist3 where
  antipode (Twist3 b xs) = Twist3 b (antiact b xs)
    where
      antiact :: Bool -> V3 a -> V3 a
      antiact c = if c then id else antipode

-- * Laws as checkable properties

-- Utility
(<++>) :: Applicative f => f String -> f String -> f String
(<++>) = liftA2 (++)

-- ** Applicative laws

leftUnit, rightUnit :: (Applicative f, Eq1 f) => f String -> Bool
leftUnit x = pure "" <++> x == x
rightUnit x = x <++> pure "" == x

associative :: (Applicative f, Eq1 f) => (f String, f String, f String) -> Bool
associative (x,y,z) = x <++> (y <++> z) == (x <++> y) <++> z

-- ** Comonoid laws

leftCounit, rightCounit, coassociative :: (Comonoid f, Eq1 f, Foldable f) => f String -> Bool
leftCounit x = erase1 (coapply x) == x
rightCounit x = erase2 (coapply x) == x
coassociative x = trans1 coapply (coapply x) == assoc (trans2 coapply (coapply x))

-- ** Has compatible Comonoid and Applicative instance.
--
-- The following laws are "automatic" and one does not need to check.
--
-- @
-- extract (pure a) = a
-- coapply (pure a) = pure a
-- @

extractAp :: (Comonoid f, Applicative f) => (f String, f String) -> Bool
extractAp (x,y) = extract (x <++> y) == extract x ++ extract y

coapplyAp :: (Comonoid f, Applicative f, Eq1 f, Foldable f) => (f String, f String) -> Bool
coapplyAp (x,y) = coapply (x <++> y) == coapply x <++> coapply y

-- ** Antipodal

leftInverse, rightInverse :: (Eq1 f, Hopf f) => f String -> Bool
leftInverse x = dap (trans1 antipode (coapply x)) == pure (extract x)
rightInverse x = dap (trans2 antipode (coapply x)) == pure (extract x)

{-
>>> -- Inputs
>>> xs = [Twist3 False (V3 "a" "b" "c"), Twist3 True (V3 "A" "B" "C")]

>>> all leftUnit xs
True
>>> all rightUnit xs
True
>>> all associative $ (,,) <$> xs <*> xs <*> xs
True
>>> all leftCounit xs
True
>>> all rightCounit xs
True
>>> all coassociative xs
True
>>> all extractAp $ (,) <$> xs <*> xs
>>> all coapplyAp $ (,) <$> xs <*> xs
True
True
>>> all leftInverse xs
True
>>> all rightInverse xs
True

-}


instance (Eq1 f, Foldable f, Eq1 g, Foldable g, Eq a) => Eq (Day f g a) where
  (==) = eq1

instance (Eq1 f, Foldable f, Eq1 g, Foldable g) => Eq1 (Day f g) where
  liftEq :: (c -> c' -> Bool) -> Day f g c -> Day f g c' -> Bool
  liftEq eq (Day fa gb op) (Day fa' gb' op')
    | null fa = boringEq fa fa' && boringEq gb gb'
    | otherwise = liftEq eqGContents fa fa'
        where
          eqG = boringEq gb gb'
          eqGContents a a' = eqG && liftEq (\b b' -> eq (op a b) (op' a' b')) (toList gb) (toList gb')

-- | > toList === toList . dayToCompose === dap . trans1 toList . trans2 toList
instance (Foldable f, Foldable g) => Foldable (Day f g) where
  null (Day fa gb _) = null fa || null gb
  length (Day fa gb _) = length fa * length gb
  foldr h r0 (Day fa gb op) = foldr (\a r -> foldr (h . op a) r gb) r0 fa
  foldMap h (Day fa gb op) = foldMap (\a -> foldMap (h . op a) gb) fa

-- | Equality ignoring its content.
--
-- If @f@ had a @Functor@ instance, 'boringEq' would be
-- equivalent to the following.
-- 
-- > boringEq fa fa' === (() <$ fa) == (() <$ fa')
boringEq :: (Eq1 f) => f a -> f a' -> Bool
boringEq = liftEq (\_ _ -> True)
