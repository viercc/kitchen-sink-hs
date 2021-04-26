{-# LANGUAGE BangPatterns #-}
module Common(Vec, sumVec, vecMax, setup) where

import Data.List (foldl')
import qualified Data.Vector.Unboxed as V

type Vec = V.Vector Int

setup :: Int -> [(Vec, Int)]
setup n = loop v0
  where
    v0 = V.replicate n 0
    loop !v = i `seq` (v, i) : loop (V.imap (+) v)
      where
        i = V.maxIndex v
{-# NOINLINE setup #-}

sumVec :: [Vec] -> Vec
sumVec = foldl' plusVec zeroVec

vecMax :: Vec -> Int
vecMax = V.maximum

plusVec :: Vec -> Vec -> Vec
plusVec x y
  | nx < ny   = plusVec y x
  | otherwise = V.imap (\i xi -> xi + (if i < ny then V.unsafeIndex y i else 0)) x
  where
    nx = V.length x
    ny = V.length y

zeroVec :: Vec
zeroVec = V.empty
