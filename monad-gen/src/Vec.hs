{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase    #-}
module Vec(Vec(), empty, singleton, vec, generate, (!), toVector, fromVector) where

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

toVector :: Vec a -> V.Vector a
toVector (Vec n f) = V.generate n f

fromVector :: V.Vector a -> Vec a
fromVector v = Vec (V.length v) (V.unsafeIndex v)

empty :: Vec a
empty = Vec 0 (\_ -> error "Vec.empty")

singleton :: a -> Vec a
singleton a = Vec 1 $ \i ->
  case i of
    0 -> a
    _ -> error $ "out of bounds:" ++ show i ++ " for Vec.singleton"

vec :: [a] -> Vec a
vec = fromVector . V.fromList

generate :: Int -> (Int -> a) -> Vec a
generate = Vec

(!) :: Vec a -> Int -> a
Vec n f ! i | 0 <= i && i < n = f i
            | otherwise       = error $ "out of bounds:" ++ show i ++ " for Vec with length " ++ show n

instance (Show a) => Show (Vec a) where
  show v = "vec " ++ show (toList v)

instance Foldable Vec where
  null (Vec n _) = n == 0
  length (Vec n _) = n
  foldMap g (Vec n f) = foldMap (g . f) [0..n-1]

instance Traversable Vec where
  traverse f v = fromVector <$> traverse f (toVector v)

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
treeMerge = foldl' (<>) empty . doublingSeq . filter (not . null)
  where
    doublingSeq = foldr step []
    step xs [] = [xs]
    step xs (ys:rest)
        | 2 * length xs <= length ys = xs : ys : rest
        | otherwise                  = step (xs <> ys) rest
