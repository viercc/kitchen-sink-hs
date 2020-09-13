{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Distributive where

import Data.Functor.Const
import Unsafe.Coerce (unsafeCoerce)
import Data.Kind (Type)

---- Example types that is Distributive
newtype Id a = Id { runId :: a }
             deriving (Show, Eq, Functor)

data Pair a = Pair { getL, getR :: a }
            deriving (Show, Eq, Functor)

---- Distributive Functor
class Functor g => Distributive g where
  distribute :: Functor f => f (g a) -> g (f a)
  collect :: (Functor f) => (a -> g b) -> f a -> g (f b)
  collect f = distribute . fmap f
  -- What laws Distributive should satisfy?

  -- fmap f = runIdentity . collect (Identity . f)
  -- fmap distribute . collect f = getCompose . collect (Compose . f)

instance Distributive ((->) r) where
  distribute f r = fmap ($ r) f

instance Distributive Id where
  distribute = Id . fmap runId

instance Distributive Pair where
  distribute f = Pair (fmap getL f) (fmap getR f)

-- Distributive implies Monad

defaultReturn :: (Distributive g) => a -> g a
defaultReturn = fmap getConst . distribute  . Const

defaultJoin :: (Distributive g) => g (g a) -> g a
defaultJoin gga = fmap (diag gga) selectors

selectors :: (Distributive g) => g (g a -> a)
selectors = distribute id

diag :: (Functor f) => f (f a) -> (f a -> a) -> a
diag ffa select = select (fmap select ffa)

{-

(<q> ... </q> means questionable)

let pure = defaultReturn
    join = defaultJoin

[fmap f . pure = pure . f]

<q>follows from free theorem</q>

[join . pure = id]

diag (pure ga) select
  = select (fmap select (pure ga))
  = select . pure $ select ga
    ~~~~~~~~~~~~~
      <q>This part has type (forall a. a -> a), thus =id</q>
  = select ga

join (pure ga)
  = fmap (diag (pure ga)) selectors
  = fmap ($ ga) selectors
  = fmap ($ ga) (distribute id)
        distribute from Distributive (r ->)
  = distribute (distribute id) ga
        distribute . distribute = id
  = id ga
  = ga

[join . fmap pure = id]

diag (fmap pure ga) select
  = select (fmap select (fmap pure ga))
  = select $ fmap (select . pure) ga
                   ~~~~~~~~~~~~~
        <q>This part has type (forall a. a -> a), thus =id</q>
  = select ga

join (fmap pure ga)
  = fmap (diag (fmap pure ga)) selectors
  = fmap ($ ga) selectors
          look previous lemma
  = ga

[join . join = join . fmap join]

join (join ggga)
  = fmap (diag (fmap (diag ggga) selectors)) selectors
  = fmap (\select -> select (fmap select (fmap (diag ggga) selectors))) selectors

-}

---- Representable Functor
class Functor f => Representable f where
  type Rep f :: Type
  index :: f a -> Rep f -> a
  tabulate :: (Rep f -> a) -> f a

  -- Must be isomorphic to ((->) (Rep f))
  --   tabulate . index = id
  --   index . tabulate = id

instance Representable ((->) r) where
  type Rep ((->) r) = r
  index = id
  tabulate = id

instance Representable Id where
  type Rep Id = ()
  index ix () = runId ix
  tabulate f = Id (f ())

instance Representable Pair where
  type Rep Pair = Bool
  index p False = getL p
  index p True = getR p
  tabulate f = Pair (f False) (f True)

---- Representable => Distributive
newtype Repr f x = Repr { runRepr :: f x }
                 deriving (Show, Eq, Functor)

instance Representable f => Representable (Repr f) where
  type Rep (Repr f) = Rep f
  index = index . runRepr
  tabulate = Repr . tabulate

instance Representable f => Distributive (Repr f) where
  distribute = tabulate . distribute . fmap index

---- Distributive => Representable
newtype Distr g x = Distr { runDistr :: g x }
                  deriving (Show, Eq, Functor)

instance Distributive g => Distributive (Distr g) where
  distribute = Distr . distribute . fmap runDistr

newtype Key f = Key { getKey :: forall x. f x -> x }

instance Distributive g => Representable (Distr g) where
  type Rep (Distr g) = Key (Distr g)
  index distr key = getKey key distr
  tabulate f = fmap f tableD

tableD :: Distributive g => g (Key g)
tableD = fmap unsafeCoerce $ distribute id
  {- id :: forall a. g a -> g a
     distribute id :: forall a. g (g a -> a)
     tableD :: g (Key g) = g (forall a. g a -> a)   -}
