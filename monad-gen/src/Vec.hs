{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase    #-}
module Vec(
  Vec(),
  empty, singleton, generate,
  toList, fromList, vec,
  toVector, fromVector,
  
  imap, indexed, iota,
  
  zipWith, zipWith3, zip, zip3,
  alignWith,
  
  (!),

  filter, mapMaybe,

) where

import Prelude hiding (zipWith, zipWith3, zip, zip3, filter)
import qualified Prelude
import qualified Data.Maybe (mapMaybe)

import qualified Control.Applicative
import Control.Monad
import Control.Monad.Fix

import Data.Semigroup
import Data.Foldable
import qualified Data.Vector as V

----------------------------------------
-- Vector

data Vec a = Vec !Int (Int -> a)
    deriving Functor

-- * Core construction
empty :: Vec a
empty = Vec 0 (\_ -> error "Vec.empty")

singleton :: a -> Vec a
singleton a = Vec 1 (const a)

generate :: Int -> (Int -> a) -> Vec a
generate n = Vec (max n 0)

-- * Accessing
(!) :: Vec a -> Int -> a
Vec n f ! i | 0 <= i && i < n = f i
            | otherwise       = error $ "out of bounds:" ++ show i ++ " for Vec with length " ++ show n

-- * Conversion
toVector :: Vec a -> V.Vector a
toVector (Vec n f) = V.generate n f

fromVector :: V.Vector a -> Vec a
fromVector v = Vec (V.length v) (V.unsafeIndex v)

fromList, vec :: [a] -> Vec a
vec = fromVector . V.fromList
fromList = vec

-- * Index
imap :: (Int -> a -> b) -> Vec a -> Vec b
imap u (Vec n f) = Vec n (\i -> u i (f i))

indexed :: Vec a -> Vec (Int, a)
indexed = imap (,)

iota :: Int -> Vec Int
iota n = Vec n id

-- * Zip/Align
zip :: Vec a -> Vec b -> Vec (a, b)
zip = zipWith (,)

zip3 :: Vec a -> Vec b -> Vec c -> Vec (a, b, c)
zip3 = zipWith3 (,,)

zipWith :: (a -> b -> c) -> Vec a -> Vec b -> Vec c
zipWith u (Vec n f) (Vec m g) = Vec (min n m) (\i -> u (f i) (g i))

zipWith3 :: (a -> b -> c -> d) -> Vec a -> Vec b -> Vec c -> Vec d
zipWith3 u as bs cs = zipWith ($) (zipWith u as bs) cs

alignWith :: (a -> r) -> (b -> r) -> (a -> b -> r) -> Vec a -> Vec b -> Vec r
alignWith this that these (Vec n f) (Vec m g) = Vec (max n m) h
  where h | n < m     = \i -> if i < n then these (f i) (g i) else that (g i)
          | n == m    = \i -> these (f i) (g i)
          | otherwise = \i -> if i < m then these (f i) (g i) else this (f i)

-- * Non-lazy operations: resulted Vec will be backed by concrete Vectors
filter :: (a -> Bool) -> Vec a -> Vec a
filter p = vec . Prelude.filter p . toList

mapMaybe :: (a -> Maybe b) -> Vec a -> Vec b
mapMaybe f = vec . Data.Maybe.mapMaybe f . toList

instance (Show a) => Show (Vec a) where
  show v = "vec " ++ show (toList v)

instance Foldable Vec where
  null (Vec n _) = n == 0
  length (Vec n _) = n
  foldMap g (Vec n f) = foldMap (g . f) [0..n-1]

instance Traversable Vec where
  traverse f (Vec n g) = fromVector <$> traverse (f . g) (V.generate n id)
  mapM f (Vec n g) = fromVector <$> mapM (f . g) (V.generate n id)

instance Applicative Vec where
  pure = singleton
  Vec m f <*> Vec n g = Vec (m * n) h
    where h i = f (i `div` n) (g (i `mod` n))
  Vec m _  *> Vec n g = Vec (m * n) h
    where h i = g (i `mod` n)
  Vec m f <*  Vec n _ = Vec (m * n) h
    where h i = f (i `div` n)

instance Control.Applicative.Alternative Vec where
  empty = empty
  (<|>) = (<>)

instance Monad Vec where
  return = pure
  ma >>= k | n <= 0   = empty
           | n <= 255 = foldMap k ma
           | otherwise = treeMerge (k <$> toList ma)
    where n = length ma
  (>>) = (*>)

instance MonadFail Vec where
  fail _ = empty

instance MonadPlus Vec where
  mzero = empty
  mplus = (<>)

instance MonadFix Vec where
  mfix f = Vec n h
    where bottom = error "Argument of mfix (f :: a -> m a) shouldn't force its argument!"
          n = length (f bottom)
          h i = fix (\a -> f a ! i)

instance (Eq a) => Eq (Vec a) where
  v1 == v2 = length v1 == length v2 && toList v1 == toList v2

instance (Ord a) => Ord (Vec a) where
  compare v1 v2 = compare (toList v1) (toList v2)

instance Semigroup (Vec a) where
  Vec 0 _ <> b       = b
  a       <> Vec 0 _ = a
  Vec m f <> Vec n g = Vec (m + n) h
    where h i = if i < m then f i else g (i - m)

  stimes n a | n >= 0    = Vec (fromIntegral n) id *> a
             | otherwise = error ("Negative exponent:" ++ show (toInteger n))
  sconcat = treeMerge . toList

instance Monoid (Vec a) where
  mempty = empty
  mconcat = treeMerge

treeMerge :: [Vec a] -> Vec a
treeMerge = foldl' (flip (<>))  empty . doublingSeq . Prelude.filter (not . null)
  where
    doublingSeq = foldl' step []
    step [] xs = [xs]
    step (ys:rest) xs
        | 2 * length xs <= length ys = xs : ys : rest
        | otherwise                  = step rest (ys <> xs)
