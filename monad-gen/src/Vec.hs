{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase    #-}
module Vec(Vec(), empty, singleton, vec, generate, (!), toVector, fromVector) where

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
  length (Vec n _) = n
  foldMap g (Vec n f) = foldMap (g . f) [0..n-1]

instance Traversable Vec where
  traverse f v = fromVector <$> traverse f (toVector v)

instance Applicative Vec where
  pure = singleton
  Vec m f <*> Vec n g = Vec (m * n) h
    where h i = f (i `mod` m) (g (i `div` m))

instance (Eq a) => Eq (Vec a) where
  v1 == v2 = length v1 == length v2 && toList v1 == toList v2

instance (Ord a) => Ord (Vec a) where
  compare v1 v2 = compare (toList v1) (toList v2)

instance Semigroup (Vec a) where
  Vec m f <> Vec n g = Vec (m + n) h
    where h i = if i < m then f i else g (i - m)

instance Monoid (Vec a) where
  mempty = empty
