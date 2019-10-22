module Lattice.Classes(
  Meet(..), Join(..), HasTop(..), HasBottom(..),
  Lattice(..),
  LatticeDistributive(..),
  LatticeBounded(..),
  Heyting(..),
  LatticeDiff(..),
  LatticeComplement(..),
  Boolean(..),
  impDefault, diffDefault
) where

import           Control.Applicative

import qualified Data.Set            as Set

----------------------------------------------------
-- Classes
----------------------------------------------------

{-|
Meet semilattice.
Meet operation @\/\\@ must satisfy:

[Associativity]

  > a /\ (b /\ c) = (a /\ b) /\ c

[Commutativity]

  > a /\ b = b /\ a

[Idempotency]

  > a /\ a = a
-}
class Meet a where
  (/\) :: a -> a -> a

infixl 7 /\

{-|
Join semilattice. Join operation @\\\/@ must satisfy:

[Associativity]

  > a \/ (b \/ c) = (a \/ b) \/ c

[Commutativity]

  > a \/ b = b \/ a

[Idempotency]

  > a \/ a = a
-}

class Join a where
  (\/) :: a -> a -> a

infixl 6 \/

-- | Existence of greatest element @top@.
--
-- > a /\ top = a
-- > a \/ top = top
--
class HasTop a where
  top :: a

-- | Existence of least element @bottom@.
--
-- > a /\ bottom = bottom
-- > a \/ bottom = a
class HasBottom a where
  bottom :: a

-- | Lattice is meet and join semilattice with the Absorption law.
--
-- [Absorption]
--
--   > a \/ (a /\ b) = a /\ (a \/ b) = a
class (Meet a, Join a) => Lattice a

-- | Bounded lattice is a lattice with top and bottom.
class (Lattice a, HasBottom a, HasTop a) => LatticeBounded a

{-|

Lattice with additional Distributivity laws.

[Distributivity(@\/\\@)]

  > a /\ (b \/ c) = (a /\ b) \/ (a /\ c)

[Distributivity(@\\\/@)]

  > a \/ (b /\ c) = (a \/ b) /\ (a \/ c)
-}

class Lattice a => LatticeDistributive a

{-| A Heyting algebra is a lattice with an additional @imp@ operation.

@a \`imp\` b@ is an element which satisfies:

[ImpAdjunction]

    ∀@x@. @a \/\\ x <= b@ iff @x <= a \`imp\` b@

Assigning @a=b@ to this law, we have the maximum element @a `imp` a@.

    ∀@x@. @x <= a \`imp\` a@

All Heyting algebra is distributive lattice.

@(a `eqv` b)@ is defined as follows, but is included in the class definition
to allow instances have more efficient implementation.

[EqvDefinition]

  > a `eqv` b = (a `imp` b) /\ (b `imp` a)

-}
class (LatticeDistributive a, HasTop a) => Heyting a where
  -- | Implies operation.
  imp :: a -> a -> a
  -- | Equivalence operation.
  eqv :: a -> a -> a
  a `eqv` b = (a `imp` b) /\ (b `imp` a)

infixr 5 `imp`
infix 4 `eqv`

{-| Lattice with the /Differnece/ operation.

It can be thought as a "dual" of an Heyting algebra, which has @\\\\@ operation
instead of @imp@, and a law for it:

[DiffAdjunction]

  ∀@x@. @x ‌‌\\\/ b ≥ a@ iff @x ≥ a \\\\ b@.

This gives the minimum element @a \\\\ a@ and distributive law in the corresponding
way which an @Heyting@ algebra is.

@(a \`xor\` b)@ is defined as follows, but included in class definition
to allow instances have efficient implementation.

[XorDefinition]

  > xor a b = (a \\ b) \/ (b \\ a)

-}
class (LatticeDistributive a, HasBottom a) => LatticeDiff a where
  -- | Relative complement operation.
  (\\) :: a -> a -> a
  -- | Symmetric difference operation.
  xor :: a -> a -> a
  xor a b = (a \\ b) \/ (b \\ a)

infixl 7 \\

-- | Complemented lattice. A complement of an element @a@ is any element @b@
-- such that @a \/\\ b = bottom@ and @a \\\/ b = top@.
-- @complement a@ must be one of such an element.
class (LatticeBounded a) => LatticeComplement a where
  -- | Complement operation.
  complement :: a -> a

-- | An complemented distributive lattice is called a Boolean algebra.
--   Its complement operation is unique.
class (LatticeComplement a, Heyting a, LatticeDiff a) => Boolean a

-- | Default implementation of @⇒@ in terms of @\\\/@ and @complement@.
--   If the complement is unique, it is an only correct
--   implementation of @⇒@.
impDefault :: LatticeComplement a => a -> a -> a
impDefault a b = complement a \/ b

-- | Default implementation of @\\\\@ in terms of @\/\\@ and @complement@.
--   If complement is unique, it is an only correct
--   implementation of @\\\\@.
diffDefault :: LatticeComplement a => a -> a -> a
diffDefault a b = a /\ complement b

---------------------------------------------------------
-- Instances
---------------------------------------------------------
-- | Trivial lattice.
instance Meet () where
  _ /\ _ = ()
instance Join () where
  _ \/ _ = ()
instance HasTop () where
  top = ()
instance HasBottom () where
  bottom = ()
instance Lattice ()
instance LatticeBounded ()
instance LatticeDistributive ()
instance Heyting () where
  imp = impDefault
instance LatticeDiff () where
  (\\) = diffDefault
instance LatticeComplement () where
  complement _ = ()
instance Boolean ()

-- | Bool is a boolean algebra.
instance Meet Bool where
  (/\) = (&&)
instance Join Bool where
  (\/) = (||)
instance HasTop Bool where
  top = True
instance HasBottom Bool where
  bottom = False
instance Lattice Bool
instance LatticeBounded Bool
instance LatticeDistributive Bool
instance Heyting Bool where
  imp = (<=)
  eqv = (==)
instance LatticeDiff Bool where
  (\\) = (>)
  xor = (/=)
instance LatticeComplement Bool where
  complement = not
instance Boolean Bool

-- | Finite Set is a lattice.
instance Ord a => Meet (Set.Set a) where
  (/\) = Set.intersection
instance Ord a => Join (Set.Set a) where
  (\/) = Set.union
instance Ord a => HasBottom (Set.Set a) where
  bottom = Set.empty
instance Ord a => Lattice (Set.Set a)
instance Ord a => LatticeDistributive (Set.Set a)
instance Ord a => LatticeDiff (Set.Set a) where
  (\\) = (Set.\\)

-- | Product lattice.
instance (Meet a, Meet b) => Meet (a,b) where
  (/\) = tuple2 (/\) (/\)
instance (Join a, Join b) => Join (a,b) where
  (\/) = tuple2 (\/) (\/)
instance (HasTop a, HasTop b) => HasTop (a,b) where
  top = (top,top)
instance (HasBottom a, HasBottom b) => HasBottom (a,b) where
  bottom = (bottom, bottom)
instance (Lattice a, Lattice b) => Lattice (a,b)
instance (LatticeBounded a, LatticeBounded b) => LatticeBounded (a,b)
instance (LatticeDistributive a, LatticeDistributive b) => LatticeDistributive (a,b)
instance (Heyting a, Heyting b) => Heyting (a,b) where
  imp = tuple2 imp imp
instance (LatticeDiff a, LatticeDiff b) => LatticeDiff (a,b) where
  (\\) = tuple2 (\\) (\\)
instance (LatticeComplement a, LatticeComplement b) => LatticeComplement (a,b) where
  complement (a,a') = (complement a, complement a')
instance (Boolean a, Boolean b) => Boolean (a,b)

tuple2 :: (a -> b -> c) -> (a' -> b' -> c') -> (a,a') -> (b,b') -> (c,c')
tuple2 f g (a,a') (b,b') = (f a b,g a' b')

-- | Lattice structure on Either a b, which is determined by partial order '≤' such that:
--
-- > forall x:a y:b. Left x ≤ Right y
-- > forall x:a y:a. Left x ≤ Left y  ⇔ x ≤ y
-- > forall x:b y:b. Right x ≤ Right y  ⇔ x ≤ y
instance (Meet a, Meet b) => Meet (Either a b) where
  Left a1 /\ Left a2   = Left (a1 /\ a2)
  Left a1 /\ Right _b2 = Left a1
  Right _b1 /\ Left a2 = Left a2
  Right b1 /\ Right b2 = Right (b1 /\ b2)
instance (Join a, Join b) => Join (Either a b) where
  Left a1 \/ Left a2   = Left (a1 \/ a2)
  Left _a1 \/ Right b2 = Right b2
  Right b1 \/ Left _a2 = Right b1
  Right b1 \/ Right b2 = Right (b1 \/ b2)
instance (HasTop b) => HasTop (Either a b) where
  top = Right top
instance (HasBottom a) => HasBottom (Either a b) where
  bottom = Left bottom
instance (Lattice a, Lattice b) => Lattice (Either a b) where
instance (LatticeDistributive a, LatticeDistributive b) =>
         LatticeDistributive (Either a b)
instance (HasBottom a, HasTop b, Lattice a, Lattice b) =>
         LatticeBounded (Either a b)
instance (Heyting a, Heyting b) => Heyting (Either a b) where
  Left a1   `imp` Left a2   = Left (a1 `imp` a2)
  Left _a1  `imp` Right _b2 = top
  Right _b1 `imp` Left a2   = Left a2
  Right b1  `imp` Right b2  = Right (b1 `imp` b2)
instance (LatticeDiff a, LatticeDiff b) => LatticeDiff (Either a b) where
  Left a1   \\ Left a2   = Left (a1 \\ a2)
  Left _a1  \\ Right _b2 = bottom
  Right b1  \\ Left _a2  = Right b1
  Right b1  \\ Right b2  = Right (b1 \\ b2)

-- | Lattice structure of a function to a lattice,
-- defined by pointwise operation.
instance Meet b => Meet (a -> b) where
  (/\) = liftA2 (/\)
instance Join b => Join (a -> b) where
  (\/) = liftA2 (\/)
instance HasTop b => HasTop (a -> b) where
  top = pure top
instance HasBottom b => HasBottom (a -> b) where
  bottom = pure bottom

instance Lattice b => Lattice (a -> b)
instance LatticeBounded b => LatticeBounded (a -> b)
instance LatticeDistributive b => LatticeDistributive (a -> b)

instance Heyting b => Heyting (a -> b) where
  imp = liftA2 imp
instance LatticeDiff b => LatticeDiff (a -> b) where
  (\\) = liftA2 (\\)

instance LatticeComplement b => LatticeComplement (a -> b) where
  complement = fmap complement
instance Boolean b => Boolean (a -> b)
