{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
module Universe where

import Data.Functor.Classes(showsUnaryWith, showsBinaryWith)

import Type.Reflection
import Data.GADT.Show ( GShow(..) )
import Data.GADT.Compare (GEq(..))

import Data.HFunctor (HFunctor(..))
import Data.HFunctor.HTraversable (HTraversable(..))
import Data.HFix
import Data.HFree
import Data.HMatchable

{-
data Value a where
  Lit :: Int -> Value Int
  Nil :: Value [a]
  Cons :: Value a -> Value [a] -> Value [a]
  Pair :: Value a -> Value b -> Value (a,b)

data Pattern a where
  VarP :: Var a -> Pattern a
  LitP :: Int -> Pattern Int
  NilP :: Pattern [a]
  ConsP :: Pattern a -> Pattern [a] -> Pattern [a]
  PairP :: Pattern a -> Pattern b -> Pattern (a,b)
-}

-- The common shape between Value and Pattern!
data Shape f a where
  LitF :: Int -> Shape f Int
  NilF :: Shape f [a]
  ConsF :: f a -> f [a] -> Shape f [a]
  PairF :: f a -> f b -> Shape f (a,b)

instance (GShow f) => GShow (Shape f) where
  gshowsPrec p (LitF n) = showsUnaryWith showsPrec "LitF" p n
  gshowsPrec _ NilF     = showString "NilF"
  gshowsPrec p (ConsF a as) = showsBinaryWith gshowsPrec gshowsPrec "ConsF" p a as
  gshowsPrec p (PairF a b)  = showsBinaryWith gshowsPrec gshowsPrec "PairF" p a b

instance GShow f => Show (Shape f a) where
  showsPrec = gshowsPrec

instance HFunctor Shape where
  hmap nat tfy = case tfy of
    LitF y -> LitF y
    NilF   -> NilF
    ConsF fa fas -> ConsF (nat fa) (nat fas)
    PairF fa fb  -> PairF (nat fa) (nat fb)

instance HTraversable Shape where
  htraverse k tfa = case tfa of
    LitF a -> pure (LitF a)
    NilF   -> pure NilF
    ConsF fa fas -> ConsF <$> k fa <*> k fas
    PairF fa fb  -> PairF <$> k fa <*> k fb

instance HMatchable Shape where
  hzipMatchWith _  (LitF a)       (LitF a')      | a == a' = Just (LitF a)
  hzipMatchWith _  NilF           NilF           = Just NilF
  hzipMatchWith nu (ConsF fa fas) (ConsF ga gas) = ConsF <$> nu fa ga <*> nu fas gas
  hzipMatchWith nu (PairF fa fb)  (PairF ga gb)  = PairF <$> nu fa ga <*> nu fb gb
  hzipMatchWith _  _              _              = Nothing

-- | Typed variables
data Var a = String :::: TypeRep a
  deriving (Show, Eq)

infix 2 ::::

instance GShow Var where
  gshowsPrec = showsPrec

instance GEq Var where
  geq (x :::: tx) (y :::: ty) =
    case geq tx ty of
      Nothing -> Nothing
      Just Refl | x == y    -> Just Refl
                | otherwise -> Nothing

-- * Values
type Value = HFix Shape

lit :: Int -> Value Int
lit = HFix . LitF

nil :: Value [a]
nil = HFix NilF

cons :: Value a -> Value [a] -> Value [a]
cons a as = HFix (ConsF a as)

list :: [Value a] -> Value [a]
list = foldr cons nil

pair :: Value a -> Value b -> Value (a,b)
pair a b = HFix (PairF a b)


-- * Patterns
type Pattern = HFree Shape Var

varPat :: Var a -> Pattern a
varPat = HPure

litPat :: Int -> Pattern Int
litPat = HFree . LitF

nilPat :: Pattern [a]
nilPat = HFree NilF

consPat :: Pattern a -> Pattern [a] -> Pattern [a]
consPat a as = HFree (ConsF a as)

listPat :: [Pattern a] -> Pattern [a]
listPat = foldr consPat nilPat

pairPat :: Pattern a -> Pattern b -> Pattern (a,b)
pairPat a b = HFree (PairF a b)


---- pretty-printing

type PP f = forall a. Int -> f a -> ShowS

prettyShapePrec :: PP f -> PP (Shape f)
prettyShapePrec prettyF p shape = case shape of
  LitF a -> showsPrec 0 a
  NilF -> ("nil" ++)
  ConsF fa fas -> showParen (p > 5) (prettyF 6 fa . (" : " ++) . prettyF 5 fas) 
  PairF fa fb -> showParen True $ prettyF 0 fa . (", " ++) . prettyF 0 fb

prettyFixPrec :: (forall f. PP f -> PP (t f)) -> PP (HFix t)
prettyFixPrec prettyT p (HFix t) = prettyT (prettyFixPrec prettyT) p t

prettyFreePrec :: PP v -> (forall f. PP f -> PP (t f)) -> PP (HFree t v)
prettyFreePrec prettyV prettyT p ftv = case ftv of
    HPure va -> prettyV p va
    HFree t -> prettyT (prettyFreePrec prettyV prettyT) p t

prettyVarPrec :: PP Var
prettyVarPrec _ (varName :::: _) = (varName ++)

prettyVal :: Value a -> String
prettyVal val = prettyFixPrec prettyShapePrec 0 val ""

prettyPat :: Pattern a -> String
prettyPat pat = prettyFreePrec prettyVarPrec prettyShapePrec 0 pat ""

prettyAssignment :: Assignment Var Value -> String
prettyAssignment ((x :::: ty) :== val) = x ++ " :== " ++ prettyVal val ++ "\t:: " ++ show ty