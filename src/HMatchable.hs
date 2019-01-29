{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances  #-}
module HMatchable where

import Data.Functor.Const
import Data.Functor.Product

import Data.Type.Equality

class HFunctor (t :: (k -> *) -> k -> *) where
  hfmap :: (forall xx. f xx -> g xx) -> t f yy -> t g yy

class HFoldable (t :: (k -> *) -> k -> *) where
  hfoldMap :: (Monoid r) => (forall xx. f xx -> r) -> t f a -> r

class (HFunctor t) => HMatchable (t :: (k -> *) -> k -> *) where
  hzipMatch :: t f xx -> t g xx -> Maybe (t (Product f g) xx)
  hzipMatch = hzipMatchWith (\fx gx -> Just (Pair fx gx))
  
  hzipMatchWith :: (forall xx. f xx -> g xx -> Maybe (h xx)) ->
                   t f yy -> t g yy -> Maybe (t h yy)

{-
data Universe (a :: *) where
  Lit :: a -> Universe a
  Nil :: Universe [a]
  Cons :: Universe a -> Universe [a] -> Universe [a]
-}

data UniverseF (f :: (* -> *)) (a :: *)  where
  LitF :: Int -> UniverseF f Int
  NilF :: UniverseF f [a]
  ConsF :: f a -> f [a] -> UniverseF f [a]

instance HFunctor UniverseF where
  hfmap nat tfy = case tfy of
    LitF y -> LitF y
    NilF   -> NilF
    ConsF fa fas -> ConsF (nat fa) (nat fas)

instance HMatchable UniverseF where
  hzipMatchWith _  (LitF a)       (LitF a')      | a == a' = Just (LitF a)
  hzipMatchWith _  NilF           NilF           = Just NilF
  hzipMatchWith nu (ConsF fa fas) (ConsF ga gas) = ConsF <$> nu fa ga <*> nu fas gas
  hzipMatchWith _  _              _              = Nothing

instance HFoldable UniverseF where
  hfoldMap f tfa = case tfa of
    LitF _ -> mempty
    NilF   -> mempty
    ConsF fa fas -> f fa <> f fas

newtype HFix (t :: (k -> *) -> (k -> *)) (a :: k) = HFix (t (HFix t) a)

data HFree (t :: (k -> *) -> (k -> *))
           (f :: k -> *)
           (a :: k)
  = HPure (f a)
  | HFree (t (HFree t f) a)

-----------------------------------------

data DSum tag f = forall xx. (tag xx) :==>: (f xx)

infix 6 :==>:

class DShow f where
  dshowsPrec :: Int -> f a -> ShowS
  dshowsPrec _ fa = (dshow fa ++)

  dshow :: f a -> String
  dshow fa = dshowsPrec 0 fa []

instance (DShow tag, DShow f) => Show (DSum tag f) where
  showsPrec p (tagx :==>: fx) =
    showParen (p > 6) $ dshowsPrec 7 tagx . (" :==>: "++) . dshowsPrec 7 fx

data UniverseTRep (a :: *) where
  IntT :: UniverseTRep Int
  ListT :: UniverseTRep a -> UniverseTRep [a]

instance Eq (UniverseTRep a) where
  _ == _  = True

instance Show (UniverseTRep a) where
  show IntT = "Int"
  show (ListT a) = "[" ++ show a ++ "]"

instance DShow UniverseTRep where
  dshow = show

instance TestEquality UniverseTRep where
  testEquality IntT IntT = Just Refl
  testEquality (ListT a) (ListT b) =
    case testEquality a b of
      Nothing -> Nothing
      Just Refl -> Just Refl
  testEquality _ _ = Nothing

data Var a = NameWithType String (UniverseTRep a)
  deriving (Show, Eq)

instance DShow Var where
  dshowsPrec = showsPrec

instance TestEquality Var where
  testEquality (NameWithType x tx) (NameWithType y ty) =
    case testEquality tx ty of
      Nothing -> Nothing
      Just Refl | x == y    -> Just Refl
                | otherwise -> Nothing

dlookup :: (TestEquality tag) => tag a -> [DSum tag f] -> Maybe (f a)
dlookup _    [] = Nothing
dlookup taga ( (tagb :==>: fb) : rest) =
  case testEquality taga tagb of
    Just Refl -> Just fb
    Nothing   -> dlookup taga rest

instance DShow (HFix UniverseF) where
  dshowsPrec p (HFix tvalue) = showParen (p > 10) $ ("HFix "++) . go 11 tvalue
    where
      go :: Int -> UniverseF (HFix UniverseF) a -> ShowS
      go q (LitF n) = showParen (q > 10) $ ("LitF "++) . showsPrec 11 n
      go _ NilF     = ("NilF"++)
      go q (ConsF fa fas) = showParen (q > 10) $
        ("ConsF "++) . dshowsPrec 11 fa . (' ':) . dshowsPrec 11 fas

instance Show (HFix UniverseF a) where
  showsPrec = dshowsPrec

-----------------------------------------------

hPatternMatch :: (HFoldable t, HMatchable t) =>
  HFree t var a -> HFix t a -> Maybe (Const [DSum var (HFix t)] a)
hPatternMatch (HPure var) value = Just (Const [var :==>: value])
hPatternMatch (HFree tpat) (HFix tvalue) =
  Const . hfoldMap getConst <$> hzipMatchWith hPatternMatch tpat tvalue

type Universe    = HFix UniverseF

litVal :: Int -> Universe Int
litVal = HFix . LitF

nilVal :: Universe [a]
nilVal = HFix NilF

consVal :: Universe a -> Universe [a] -> Universe [a]
consVal a as = HFix (ConsF a as)

listVal :: [Universe a] -> Universe [a]
listVal = foldr consVal nilVal

val1 :: Universe Int
val1 = litVal 1

val2 :: Universe [a]
val2 = nilVal

val3 :: Universe [Int]
val3 = listVal (litVal <$> [1,2,3])

val4 :: Universe [[Int]]
val4 = listVal [ nilVal, listVal [litVal 1] ]

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


varX :: Var Int
varX = NameWithType "x" IntT

varY :: Var Int
varY = NameWithType "y" IntT

varXs :: Var [Int]
varXs = NameWithType "xs" (ListT IntT)

varYs :: Var [Int]
varYs = NameWithType "ys" (ListT IntT)

pat1 :: UniversePat Int
pat1 = varPat varX

pat2 :: UniversePat Int
pat2 = litPat 1

pat3 :: UniversePat [Int]
pat3 = consPat (varPat varX) (varPat varXs)

pat4 :: UniversePat [[Int]]
pat4 = listPat [varPat varXs, varPat varYs]
