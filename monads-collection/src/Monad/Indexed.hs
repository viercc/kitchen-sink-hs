{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE EmptyCase #-}

{- |

Conor McBride-style Indexed Monad

https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf

-}
module Monad.Indexed(
  -- * IxFunctor and IxMonad
  IxFunctor(..),
  IxMonad(..),

  -- * Relation between Atkey-style
  At(..), Atkey,
  ireturn', ibind',
  WrapAtkey(..),
  wrap, unwrap,

  -- * Example: Indexed State monad
  IxState(..),
  SomeTup(..),
  IxState',
  iget', iput', imodify',
  runIxState',

  -- * Example: Free Monad
  IxFree(..),
  interpret,

  -- * Indexed Applicative (Atkey-style)
  IxApplicative(..),
  (<<$>>), iap'
) where

import Data.Kind (Constraint, Type)

-- | Indexed Functor is a Functor from Hask^K to Hask^K,
--   where @K@ stands for the discrete category of types of
--   kind @k@.
--
--   That means, to @F@ to be @IxFunctor@, We don't assume input
--   functor @x@ has any instance of type class (like @Functor@
--   or @Monad@), and don't assure @F x@ to become any instance of
--   type class. All data constructors of kind @k -> *@ is already
--   an functor from discrete category.
type IxFunctor :: ((k -> Type) -> k -> Type) -> Constraint
class IxFunctor f where
  ifmap :: (forall a. x a -> y a) -> f x b -> f y b

-- | IxMonad

class (IxFunctor m) => IxMonad m where
  ireturn :: x a -> m x a
  ijoin :: m (m x) a -> m x a

  ibind :: m x b -> (forall a. x a -> m y a) -> m y b
  ibind fxb k = ijoin (ifmap k fxb)

data At a i j where
  V :: a -> At a i i

-- | Atkey-style indexed monad
type Atkey m i j a = m (At a j) i

ireturn' :: (IxMonad m) => a -> Atkey m i i a
ireturn' = ireturn . V

ibind' :: forall i j k a b m.
          (IxMonad m) =>
          Atkey m i j a -> (a -> Atkey m j k b) -> Atkey m i k b
ibind' m_ij_a f =
  let f' :: forall z. At a j z -> m (At b k) z
      f' (V a) = f a
  in m_ij_a `ibind` f'

-- | Atkey-style to Conor McBride-style
type AtkeyIxFunctor :: (k -> k -> Type -> Type) -> Constraint
class AtkeyIxFunctor f where
  ifmap_A :: (a -> b) -> f i j a -> f i j b

class AtkeyIxFunctor m => AtkeyIxMonad m where
  ireturn_A :: a -> m i i a
  
  ibind_A :: m i j a -> (a -> m j k b) -> m i k b
  ibind_A mij k = ijoin_A $ ifmap_A k mij
  
  ijoin_A :: m i j (m j k a) -> m i k a
  ijoin_A mm = ibind_A mm id

newtype WrapAtkey m x i = WrapAtkey {
    runWrapAtkey :: forall __ r. (forall j. x j -> m j __ r) -> m i __ r
  }

wrap :: AtkeyIxMonad m => m i j a -> WrapAtkey m (At a j) i
wrap ma = WrapAtkey $ \ret -> ma `ibind_A` \a -> ret (V a)

unwrap :: AtkeyIxMonad m => WrapAtkey m (At a j) i -> m i j a
unwrap m = runWrapAtkey m (\(V a) -> ireturn_A a)

instance IxFunctor (WrapAtkey f) where
  ifmap phi (WrapAtkey mij) = WrapAtkey (\ret -> mij (ret . phi))

instance IxMonad (WrapAtkey m) where
  ireturn :: x i -> WrapAtkey m x i
  ireturn xi = WrapAtkey $ \ret -> ret xi

  ijoin :: forall x i. WrapAtkey m (WrapAtkey m x) i -> WrapAtkey m x i
  ijoin (WrapAtkey mm) = WrapAtkey $ \ret -> mm (\m -> runWrapAtkey m ret)

-- | "Free monad" over IxFunctor
type IxFree :: ((k -> Type) -> k -> Type)
            -> (k -> Type) -> k -> Type
data IxFree f v a
     = Wrap (f (IxFree f v) a)
     | Pure (v a)

instance (IxFunctor f) => IxFunctor (IxFree f) where
  ifmap :: forall g h a. (forall x. g x -> h x) ->
                         IxFree f g a -> IxFree f h a
  ifmap phi =
    let go :: forall b. IxFree f g b -> IxFree f h b
        go (Wrap fpa) = Wrap $ ifmap go fpa
        go (Pure va)  = Pure $ phi va
    in go

instance (IxFunctor f) => IxMonad (IxFree f) where
  ireturn = Pure
  ijoin (Wrap fmma) = Wrap $ ifmap ijoin fmma
  ijoin (Pure ma)   = ma

interpret :: (IxMonad m) =>
  (forall r a. f r a -> m r a) -> IxFree f x b -> m x b
interpret handler (Wrap fpa) = handler fpa `ibind` interpret handler
interpret _       (Pure xa)  = ireturn xa

-- | Indexed State monad

-- | ∃t. (t, x t)
data SomeTup x = forall t. SomeTup t (x t)

-- | IxState x s = s -> ∃t. (t, x t)
newtype IxState x s = IxState (s -> SomeTup x)

instance IxFunctor IxState where
  ifmap phi (IxState st) = IxState $ \s ->
    case st s of
      SomeTup t xt -> SomeTup t (phi xt)

instance IxMonad IxState where
  ireturn xt = IxState $ \t -> SomeTup t xt
  ijoin (IxState mmxs) = IxState $ \s ->
    case mmxs s of
      SomeTup t (IxState mxt) -> mxt t

-- | Atkey-style Indexed State monad
type IxState' s t a = Atkey IxState s t a

runIxState' :: IxState' s t a -> s -> (t, a)
runIxState' (IxState st) s =
  case st s of
    SomeTup t (V a) -> (t, a)

iget' :: IxState' s s s
iget' = IxState $ \s -> SomeTup s (V s)

iput' :: t -> IxState' s t ()
iput' t = IxState $ \_ -> SomeTup t (V ())

imodify' :: (s -> t) -> IxState' s t ()
imodify' f = IxState $ \s -> SomeTup (f s) (V ())


-- | Atkey-style indexed Applicative

class (IxFunctor f) => IxApplicative f where
  ipure :: a -> Atkey f i i a
  (<<*>>) :: Atkey f i j (a -> b) -> Atkey f j k a -> Atkey f i k b

(<<$>>) :: IxFunctor f =>
           (a -> b) -> Atkey f i j a -> Atkey f i j b
f <<$>> fa = ifmap (\(V a) -> V (f a)) fa

iap' :: (IxMonad m) =>
       Atkey m i j (a -> b) -> Atkey m j k a -> Atkey m i k b
iap' mab ma = ibind' mab (<<$>> ma)

instance IxApplicative IxState where
  ipure = ireturn'
  (<<*>>) = iap'

{-

-- * IxMonoidal /= IxApplicative
--
-- Monoidal structure of Hask^K: Unit and (:*:)
data Unit (a :: k) = Unit
   deriving (Show, Read, Eq, Ord)

data (:*:) f g (a :: k) = f a :*: g a
   deriving (Show, Read, Eq, Ord)

class (IxFunctor f) => IxMonoidal f where
  iunit :: f Unit a
  iprod :: f x a -> f y a -> f (x :*: y) a

unit2pure :: (IxMonoidal f) => (forall a. x a) -> f x b
unit2pure xa = ifmap (const xa) iunit

prod2liftA2 ::
  forall f x y z.
    (IxMonoidal f) =>
      (forall a. x a -> y a -> z a) ->
      (forall b. f x b -> f y b -> f z b)
prod2liftA2 phi fxb fyb =
  ifmap (\(xa :*: ya) -> phi xa ya) (iprod fxb fyb)

-}
