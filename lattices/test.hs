module Main(main) where

import Searchable

import Text.Read(Read(..))

-- * Examples

data Nat = Z | S Nat
         deriving (Eq, Ord)

instance Show Nat where
  show = show . conv (0 :: Integer)
    where conv accum Z     = accum
          conv accum (S n) = accum `seq` conv (accum+1) n

instance Read Nat where
  readPrec = fromInteger <$> readPrec

instance Num Nat where
  fromInteger x | x <= 0 = Z
                | otherwise = S (fromInteger (x-1))
  Z   + y = y
  S x + y = S (x + y)
  Z   * _ = Z
  S x * y = y + x * y
  abs = id
  signum Z     = Z
  signum (S _) = S Z
  (-) = undefined

nats :: Set Nat
nats = singleton Z `union` fmap S nats

example1 :: Maybe Nat
example1 = search nats $ \n -> n*n == 25

example2 :: Maybe Nat
example2 = search nats $ \n -> n*n == 24

-- | DON'T pass empty or infinite list!
oneOf :: [a] -> Set a
oneOf []     = error "Set can't be empty!"
oneOf (x:[]) = singleton x
oneOf (x:xs) = singleton x `union` oneOf xs {-  xs /= []  -}

stringOf :: Set a -> Set [a]
stringOf xs = singleton [] `union` ((:) <$> xs <*> stringOf xs)

lengthNat :: [a] -> Nat
lengthNat = foldr (\_ n -> S n) Z

example3 :: Maybe (Char, Char)
example3 =
  search (prod (oneOf "abcde") (oneOf "efghi")) $
    \(x,y) -> x == y

example4 :: Maybe [Bool]
example4 =
  search (stringOf bit) $
    \str -> lengthNat str == 4 &&
            reverse str == fmap not str

example5 :: Maybe [Int]
example5 =
  search (stringOf (oneOf [0..4])) $
    \str -> lengthNat str == 12 && messed str
  where
    a <+> b = (a + b) `mod` 5
    messed = messed' (0,0,0,0,0)
    messed' _ [] = True
    messed' (p,q,r,s,t) (a:as) =
      (p /= a) && (q /= a) && (r /= a) && (s /= a) && (t /= a) &&
      messed' (q <+> 1, r, s, t, p <+> p <+> a) as

main :: IO ()
main = do
  print example1
  print example2
  print example3
  print example4
  print example5
