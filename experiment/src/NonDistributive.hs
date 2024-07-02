{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveTraversable #-}
module NonDistributive where

import Control.Monad (ap)
import Data.Foldable (toList)
import Data.Bifunctor (Bifunctor(..))
import Data.Bifoldable (Bifoldable(..))

import Data.Functor.Classes
import Text.Show (showListWith)

-- * NotOne

data NotOne a = Zero | TwoOrMore a a [a]
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable)

notOne :: [a] -> Either a (NotOne a)
notOne [] = Right Zero
notOne [a] = Left a
notOne (a1 : a2 : as) = Right (TwoOrMore a1 a2 as)

-- * Mutually recursive tree

newtype Mutual f g a = Mutual (f (Either a (Mutual g f a)))

instance (Functor f, Functor g) => Functor (Mutual f g) where
  fmap h (Mutual x) = Mutual $ fmap (bimap h (fmap h)) x

instance (Foldable f, Foldable g) => Foldable (Mutual f g) where
  foldMap h (Mutual x) = foldMap (bifoldMap h (foldMap h)) x

-- * Expr

data Expr a =
    Var a
  | SumStart (Mutual SumF ProdF a)
  | ProdStart (Mutual ProdF SumF a)
  deriving (Functor)

newtype SumF a = SumOf (NotOne a)
  deriving (Functor, Foldable)

newtype ProdF a = ProdOf (NotOne a)
  deriving (Functor, Foldable)

-- | View Expr as sum of products
viewSum :: Expr a -> [Either a (Mutual ProdF SumF a)]
viewSum mx = case mx of
  Var x -> [Left x]
  SumStart (Mutual subterms) -> toList subterms
  ProdStart subterms -> [Right subterms]

-- | Take sum of exprs
sumE :: [Expr a] -> Expr a
sumE xs = case notOne (xs >>= viewSum) of
  Left (Left x) -> Var x
  Left (Right px) -> ProdStart px
  Right sx -> SumStart . Mutual . SumOf $ sx

-- | View Expr as product of sums
viewProd :: Expr a -> [Either a (Mutual SumF ProdF a)]
viewProd mx = case mx of
  Var x -> [Left x]
  SumStart subterms -> [Right subterms]
  ProdStart (Mutual subterms) -> toList subterms

-- | Take product of exprs
prodE :: [Expr a] -> Expr a
prodE xs = case notOne (xs >>= viewProd) of
  Left (Left x) -> Var x
  Left (Right sx) -> SumStart sx
  Right px -> ProdStart . Mutual . ProdOf $ px

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  mx >>= k = join_ (fmap k mx)
    where
      join_ (Var mb) = mb
      join_ (SumStart smb) = foldMutual (sumE . toList) (prodE . toList) smb
      join_ (ProdStart pmb) = foldMutual (prodE . toList) (sumE . toList) pmb

foldMutual :: forall f g r. (Functor f, Functor g) => (f r -> r) -> (g r -> r) -> Mutual f g r -> r
foldMutual fAlg gAlg (Mutual x) = fAlg (fmap (either id (foldMutual gAlg fAlg)) x)

-------------------


instance Show a => Show (SumF a) where
  showsPrec = showsPrec1

instance Show1 SumF where
  liftShowsPrec _ showl _ (SumOf as) = ("sum" ++) . showl (toList as)

instance Show a => Show (ProdF a) where
  showsPrec = showsPrec1

instance Show1 ProdF where
  liftShowsPrec _ showl _ (ProdOf as) = ("prod" ++) . showl (toList as)

instance (Show a) => Show (Expr a) where
  showsPrec = showsPrec1

instance Show1 Expr where
  liftShowsPrec showsp showl p mx = case mx of
    Var x -> showsp 0 x
    SumStart sx -> liftShowsPrec showsp showl p sx
    ProdStart px -> liftShowsPrec showsp showl p px

instance (Show a, Show1 f, Show1 g)
  => Show (Mutual f g a) where
  showsPrec = showsPrec1

instance (Show1 f, Show1 g) => Show1 (Mutual f g) where
  liftShowsPrec showsp _ p (Mutual fx) = liftShowsPrec' step p fx
    where
      step p' (Left a) = showsp p' a
      step p' (Right x) = liftShowsPrec' showsp p' x

liftShowsPrec' :: Show1 f => (Int -> a -> ShowS) -> Int -> f a -> ShowS
liftShowsPrec' showsp = liftShowsPrec showsp (showListWith (showsp 0))

------------

-- * test
--
-- >>> sumE [ prodE [pure 10, pure 20], sumE [], prodE [], sumE [pure 30, pure 40] ]
-- sum[prod[10,20],prod[],30,40]
