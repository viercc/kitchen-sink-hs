{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module KrohnRhodes where

import Control.Monad.State
import Data.Bifunctor
import Data.Finitary
import Data.Finite
import Data.Kind
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Data.Profunctor
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.TypeLits (natVal)

-- | Finite state machine.
newtype Machine s a b = Machine {_transit :: a -> s -> (b, s)}

deriving instance Functor (Machine s a)

instance Profunctor (Machine s) where
  rmap = fmap
  lmap f (Machine tr) = Machine (tr . f)
  dimap f g (Machine tr) = Machine (\a' -> first g . tr (f a'))

pass :: Machine any a a
pass = Machine (,)

(***) :: Machine s a b -> Machine t a' b' -> Machine (s, t) (a, a') (b, b')
Machine tr1 *** Machine tr2 = Machine tr
  where
    tr (a, b) (x, y) =
      let ~(a', x') = tr1 a x
          ~(b', y') = tr2 b y
       in ((a', b'), (x', y'))

cascade :: Machine s a b -> Machine t b c -> Machine (s, t) a c
Machine tr1 `cascade` Machine tr2 = Machine tr
  where
    tr a (x, y) =
      let (b, x') = tr1 a x
          (c, y') = tr2 b y
       in (c, (x', y'))

stateSize :: forall s a b. Finitary s => Machine s a b -> Integer
stateSize _ = natVal @(Cardinality s) Proxy

-- Step through multiple input symbols. Typically, input symbols are a list
--
-- > transitMany :: Machine a b -> [a] -> s -> ([b], s)
--
-- But this function works with arbitrary 'Traversable' containers, not just
-- lists.
transitMany :: Traversable f => Machine s a b -> f a -> s -> (f b, s)
transitMany (Machine tr) as = runState (traverse (state . tr) as)

isSurjection :: forall k s. (Finitary s) => Map k s -> Bool
isSurjection f = setSize == Set.size range
  where
    range = Set.fromList $ map toFinite $ Map.elems f
    setSize = fromInteger $ natVal @(Cardinality s) Proxy

forAll :: Foldable t => t a -> (a -> Bool) -> Bool
forAll = flip all

{-

     cover
 S? <------- T
  |          |
  | ms a     | mt a
  v          v
(S?,B) <-- (T,B)
  first cover

-}

isDivisionOf :: (Finitary a, Ord s, Finitary s, Ord t, Finitary t, Eq b) => Map t s -> Machine s a b -> Machine t a b -> Bool
isDivisionOf cover ms mt = isSurjection cover && coherent
  where
    coherent =
      forAll inhabitants $ \a ->
        forAll (Map.toList cover) $ \(t, s) ->
          let (b1, s1) = _transit ms a s -- _transit ms a (cover ! t)
              (b2, t2) = _transit mt a t
           in (b1, Just s1) == (b2, cover !? t2)
