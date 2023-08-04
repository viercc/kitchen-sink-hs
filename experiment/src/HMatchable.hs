{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module HMatchable where

import Data.Kind (Type, Constraint)

import Data.Functor.Const

import Data.Functor.Classes(showsUnaryWith, showsBinaryWith)

import Type.Reflection
import Data.GADT.Show ( GShow(..) )
import Data.GADT.Compare (GEq(..))

type  HFunctor :: ((k -> Type) -> k -> Type) -> Constraint
class HFunctor t where
  hfmap :: (forall xx. f xx -> g xx) -> t f yy -> t g yy

type  HFoldable :: ((k -> Type) -> k -> Type) -> Constraint
class HFoldable t where
  hfoldMap :: (Monoid r) => (forall xx. f xx -> r) -> t f a -> r

type  HMatchable :: ((k -> Type) -> k -> Type) -> Constraint
class (HFunctor t) => HMatchable t where
  hzipMatchWith :: (forall xx. f xx -> g xx -> Maybe (h xx)) ->
                   t f yy -> t g yy -> Maybe (t h yy)

{-
data Universe a where
  Lit :: a -> Universe a
  Nil :: Universe [a]
  Cons :: Universe a -> Universe [a] -> Universe [a]
  Pair :: Universe a -> Universe b -> Universe (a,b)
-}

data UniverseF f a where
  LitF :: Int -> UniverseF f Int
  NilF :: UniverseF f [a]
  ConsF :: f a -> f [a] -> UniverseF f [a]
  PairF :: f a -> f b -> UniverseF f (a,b)

instance (GShow f) => GShow (UniverseF f) where
  gshowsPrec p (LitF n) = showsUnaryWith showsPrec "LitF" p n
  gshowsPrec _ NilF     = showString "NilF"
  gshowsPrec p (ConsF a as) = showsBinaryWith gshowsPrec gshowsPrec "ConsF" p a as
  gshowsPrec p (PairF a b)  = showsBinaryWith gshowsPrec gshowsPrec "PairF" p a b

instance GShow f => Show (UniverseF f a) where
  showsPrec = gshowsPrec

instance HFunctor UniverseF where
  hfmap nat tfy = case tfy of
    LitF y -> LitF y
    NilF   -> NilF
    ConsF fa fas -> ConsF (nat fa) (nat fas)
    PairF fa fb  -> PairF (nat fa) (nat fb)

instance HMatchable UniverseF where
  hzipMatchWith _  (LitF a)       (LitF a')      | a == a' = Just (LitF a)
  hzipMatchWith _  NilF           NilF           = Just NilF
  hzipMatchWith nu (ConsF fa fas) (ConsF ga gas) = ConsF <$> nu fa ga <*> nu fas gas
  hzipMatchWith nu (PairF fa fb)  (PairF ga gb)  = PairF <$> nu fa ga <*> nu fb gb
  hzipMatchWith _  _              _              = Nothing

instance HFoldable UniverseF where
  hfoldMap f tfa = case tfa of
    LitF _ -> mempty
    NilF   -> mempty
    ConsF fa fas -> f fa <> f fas
    PairF fa fb  -> f fa <> f fb

type HFix :: ((k -> Type) -> k -> Type) -> k -> Type
newtype HFix t a = HFix (t (HFix t) a)

instance GShow (t (HFix t)) => GShow (HFix t) where
  gshowsPrec p (HFix tt) = showsUnaryWith gshowsPrec "HFix" p tt

instance GShow (t (HFix t)) => Show (HFix t a) where
  showsPrec = gshowsPrec

type HFree :: ((k -> Type) -> k -> Type) -> (k -> Type) -> k -> Type
data HFree t f a
  = HPure (f a)
  | HFree (t (HFree t f) a)

instance (GShow f, GShow (t (HFree t f))) => GShow (HFree t f) where
  gshowsPrec p (HPure fa) = showsUnaryWith gshowsPrec "HPure" p fa
  gshowsPrec p (HFree tfa) = showsUnaryWith gshowsPrec "HFree" p tfa

instance (GShow f, GShow (t (HFree t f))) => Show (HFree t f a) where
  showsPrec = gshowsPrec

-----------------------------------------

infix 2 ::::
data Var a = String :::: TypeRep a
  deriving (Show, Eq)

instance GShow Var where
  gshowsPrec = showsPrec

instance GEq Var where
  geq (x :::: tx) (y :::: ty) =
    case geq tx ty of
      Nothing -> Nothing
      Just Refl | x == y    -> Just Refl
                | otherwise -> Nothing


-----

infix 1 :==
data Assignment tag f where
  (:==) :: tag a -> f a -> Assignment tag f

instance (GShow tag, GShow f) => Show (Assignment tag f) where
  showsPrec p (tag :== f) = showParen (p < 1) $ gshowsPrec 1 tag . (" :== " ++) . gshowsPrec 1 f

dlookup :: (GEq tag) => tag a -> [Assignment tag f] -> Maybe (f a)
dlookup _    [] = Nothing
dlookup taga ( (tagb :== fb) : rest) =
  case geq taga tagb of
    Just Refl -> Just fb
    Nothing   -> dlookup taga rest

-----------------------------------------------

hPatternMatch :: (HFoldable t, HMatchable t) =>
  HFree t var a -> HFix t a -> Maybe [Assignment var (HFix t)]
hPatternMatch (HPure var) value = Just [var :== value]
hPatternMatch (HFree tpat) (HFix tvalue) =
  hfoldMap getConst <$> hzipMatchWith (\pat var -> Const <$> hPatternMatch pat var) tpat tvalue

type Universe = HFix UniverseF

litVal :: Int -> Universe Int
litVal = HFix . LitF

nilVal :: Universe [a]
nilVal = HFix NilF

consVal :: Universe a -> Universe [a] -> Universe [a]
consVal a as = HFix (ConsF a as)

listVal :: [Universe a] -> Universe [a]
listVal = foldr consVal nilVal

pairVal :: Universe a -> Universe b -> Universe (a,b)
pairVal a b = HFix (PairF a b)

val1 :: Universe Int
val1 = litVal 1

val2 :: Universe [a]
val2 = nilVal

val3 :: Universe [Int]
val3 = listVal (litVal <$> [1,2,3])

val4 :: Universe [[Int]]
val4 = listVal [ nilVal, listVal [litVal 1] ]

val5 :: Universe (Int, [Int])
val5 = pairVal val1 val3

type UniversePat = HFree UniverseF Var

varPat :: Var a -> UniversePat a
varPat = HPure

litPat :: Int -> UniversePat Int
litPat = HFree . LitF

nilPat :: UniversePat [a]
nilPat = HFree NilF

consPat :: UniversePat a -> UniversePat [a] -> UniversePat [a]
consPat a as = HFree (ConsF a as)

listPat :: [UniversePat a] -> UniversePat [a]
listPat = foldr consPat nilPat

pairPat :: UniversePat a -> UniversePat b -> UniversePat (a,b)
pairPat a b = HFree (PairF a b)

varX, varY :: Var Int
varX = "x" :::: typeRep
varY = "y" :::: typeRep

varXs, varYs :: Var [Int]
varXs = "xs" :::: typeRep
varYs = "ys" :::: typeRep

pat1 :: UniversePat Int
pat1 = varPat varX

pat2 :: UniversePat Int
pat2 = litPat 1

pat3 :: UniversePat [Int]
pat3 = consPat (varPat varX) (varPat varXs)

pat4 :: UniversePat [[Int]]
pat4 = listPat [varPat varXs, varPat varYs]

pat5 :: UniversePat (Int, [Int])
pat5 = pairPat (varPat varX) (consPat (varPat varY) (varPat varYs))

