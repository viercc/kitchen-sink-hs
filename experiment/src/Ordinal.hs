{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf   #-}
module Ordinal(
  Ordinal(),
  omega,
  OrdinalView(..),
  view,

  hardy, hardy_eps0
) where

type Natural = Integer

-- | Ordinal numbers represented by Cantor Normal Form
newtype Ordinal = CNF [(Ordinal, Natural)]
                deriving (Eq, Ord)

omega :: Ordinal -> Ordinal
omega a = CNF [(a,1)]

addOrdinal :: Ordinal -> Ordinal -> Ordinal
addOrdinal x (CNF []) = x
addOrdinal (CNF xs) (CNF (y:ys)) = CNF $ loop xs
  where
    loop [] = y:ys
    loop ((e,n):zs) =
      case compare e (fst y) of
        GT -> (e,n) : loop zs
        EQ -> let !n' = n + snd y in (e,n') : ys
        LT -> y:ys

multOrdinal :: Ordinal -> Ordinal -> Ordinal
multOrdinal (CNF xs) (CNF ys) = foldr addOrdinal 0 $ fmap (multOne xs) ys
  where
    multOne []     _     = 0
    multOne ((e,n):as) (f,m) =
      if f == 0
      then let !n' = n * m in CNF ((e, n') : as)
      else omega (addOrdinal e f)

instance Num Ordinal where
    fromInteger n
      | n < 0     = error "Not a natural number"
      | n == 0    = CNF []
      | otherwise = CNF [(0, n)]
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

instance Show Ordinal where
  showsPrec = sprec where
    sprec _ (CNF []) = ("0"++)
    sprec p (CNF xs) = (intercalate' (const id) plus $ fmap conv xs) p

    conv (e,n) q =
      let strE = if e == 1 then ("ω"++) else ("ω^"++) . sprec 8 e
          strN = shows n
      in if | e == 0     -> strN
            | n == 1     -> strE
            | otherwise  -> parensIf' (q>4) (strE . ('*':) . strN)
    plus a b = \q -> parensIf' (q>3) (a 2 . (" + " ++) . b 3)

data OrdinalView = Zero | Succ Ordinal | Lim (Natural -> Ordinal)

view :: Ordinal -> OrdinalView
view (CNF []) = Zero
view (CNF [(e,1)]) =
  case view e of
    Zero    -> Succ 0
    Succ e' -> Lim (\n -> CNF [(e',n)])
    Lim f   -> Lim (\n -> omega (f n))
view (CNF [(e,n)]) = consView (e,n-1) (view (CNF [(e,1)]))
view (CNF (x:xs))  = consView x (view (CNF xs))

consView :: (Ordinal, Natural) -> OrdinalView -> OrdinalView
consView x Zero            = Succ (CNF [x])
consView x (Succ (CNF xs)) = Succ (CNF (x:xs))
consView x (Lim f)         = Lim (\n -> case f n of CNF xs -> CNF (x:xs))

instance Show OrdinalView where
  show Zero = "<Zero>"
  show (Succ n) = "<Succ " ++ (showsPrec 9 n ">")
  show (Lim f)  = "<" ++ s 1 ++ ", " ++ s 2 ++ ", " ++ s 3 ++ ", ...>"
    where s = show . f

-- | Hardy hierarchy
hardy :: Ordinal -> Integer -> Integer
hardy x !n = case view x of
  Zero    -> n
  Succ x' -> hardy x' (1 + n)
  Lim f   -> hardy (f n) n

hardy_eps0 :: Integer -> Integer
hardy_eps0 n = hardy (nTimes n omega 0) n
  where
    nTimes 0 _ x = x
    nTimes m f x = f (nTimes (m-1) f x)
