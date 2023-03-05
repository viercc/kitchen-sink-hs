{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf   #-}
module Ordinal(
  CNF(),
  omega,
  OrdinalView(..),
  view,

  hardy, hardy_eps0
) where

import Data.Ord (comparing)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Numeric.Natural
import Data.Maybe (fromMaybe)

-- | CNF numbers represented by Cantor Normal Form
newtype CNF = MkCNF { toMap :: Map CNF Natural }
                deriving (Eq)

instance Ord CNF where
  compare = comparing (Map.toDescList . toMap)

zero :: CNF
zero = MkCNF Map.empty

fromNatural :: Natural -> CNF
fromNatural 0 = zero
fromNatural k = MkCNF $ Map.singleton zero k

omega :: CNF -> CNF
omega a = MkCNF $ Map.singleton a 1

addOrdinal :: CNF -> CNF -> CNF
addOrdinal x (MkCNF ys) = case Map.maxViewWithKey ys of
  Nothing -> x
  Just ((y,n),ys') -> case Map.splitLookup y (toMap x) of
    (_xsLow, maybeM, xsHigh) ->
      let n' = fromMaybe 0 maybeM + n
       in MkCNF $ Map.union xsHigh (Map.insert y n' ys')

multOrdinal :: CNF -> CNF -> CNF
multOrdinal (MkCNF xs) (MkCNF ys) = case Map.maxViewWithKey xs of
  Nothing -> zero
  Just ((e,n),xsLow) ->
    MkCNF $ Map.fromDistinctDescList $ do
      (f,m) <- Map.toDescList ys
      if f == zero
        then (e, n * m) : Map.toDescList xsLow
        else [ (addOrdinal e f, m) ]

instance Num CNF where
    fromInteger n
      | n < 0     = error "Not a natural number"
      | otherwise = fromNatural (fromInteger n)
    (+) = addOrdinal
    (*) = multOrdinal
    (-) = error "No Subtraction"
    abs = id
    signum x = if x == 0 then 0 else 1

intercalate' :: a -> (a -> a -> a) -> [a] -> a
intercalate' z _ []      = z
intercalate' _ _ [x]     = x
intercalate' z op (x:xs) = op x (intercalate' z op xs)

parensIf' :: Bool -> ShowS -> ShowS
parensIf' True  x = ('(':) . x . (')':)
parensIf' False x = x

instance Show CNF where
  showsPrec = sprec where
    sprec p x = showSum p (Map.toDescList (toMap x))
    showSum _ [] = ("0" ++)
    showSum p xs = (intercalate' (const id) plus $ fmap showTerm xs) p
    
    showTerm (e,n) q =
      let strE = if e == 1 then ("ω"++) else ("ω^"++) . sprec 8 e
          strN = shows n
      in if | e == 0     -> strN
            | n == 1     -> strE
            | otherwise  -> parensIf' (q>4) (strE . ('*':) . strN)
    plus a b q = parensIf' (q>3) (a 2 . (" + " ++) . b 3)

data OrdinalView a = Zero | Succ a | Lim (Natural -> a)

view :: CNF -> OrdinalView CNF
view (MkCNF xs) = case Map.minViewWithKey xs of
  Nothing -> Zero
  Just ((e,n),xsHigh) ->
    let x' | n > 1    = MkCNF $ Map.insert e (n - 1) xsHigh
           | otherwise = MkCNF xsHigh
    in case view e of
         Zero -> Succ x'
         Succ e' -> Lim (\k -> x' + omega e' * fromNatural k)
         Lim f   -> Lim (\k -> x' + omega (f k))

instance Show a => Show (OrdinalView a) where
  show Zero = "<Zero>"
  show (Succ n) = "<Succ " ++ showsPrec 9 n ">"
  show (Lim f)  = "<" ++ s 1 ++ ", " ++ s 2 ++ ", " ++ s 3 ++ ", ...>"
    where s = show . f

-- | Hardy hierarchy
hardy :: CNF -> Natural -> Natural
hardy x !n = case view x of
  Zero    -> n
  Succ x' -> hardy x' (1 + n)
  Lim f   -> hardy (f n) n

hardy_eps0 :: Natural -> Natural
hardy_eps0 n = hardy (nTimes n omega 0) n
  where
    nTimes 0 _ x = x
    nTimes m f x = f (nTimes (m-1) f x)
