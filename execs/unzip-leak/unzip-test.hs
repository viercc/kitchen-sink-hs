{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
module Main(main) where

import Data.List (unzip, foldl')
import qualified Data.Vector.Unboxed as V

type Vec = V.Vector Int

-- Set the CPP parameter UNZIP_FUNCTION to either
-- 'unzipList' or 'unzipFunctor'
main :: IO ()
main = do
  let (x,y) = summarize $ UNZIP_FUNCTION $ take 10_000 $ setup 10_000
  print x
  print y

unzipList :: [(a,b)] -> ([a], [b])
unzipList = unzip

unzipFunctor :: Functor f => f (a,b) -> (f a, f b)
unzipFunctor fab = (fst <$> fab, snd <$> fab)

-------------------------------------------------

setup :: Int -> [(Vec, Int)]
setup n = loop v0
  where
    v0 = V.replicate n 0
    loop !v = i `seq` (v, i) : loop (V.imap (+) v)
      where
        i = V.maxIndex v
{-# NOINLINE setup #-}

summarize :: ([Vec], [Int]) -> (Int, Int)
summarize ([],_) = error "Must be nonempty list!"
summarize (v:vs, maxIndices) = (sumOfMax, maxIndices !! 10)
  where
    sumOfMax = V.sum $ foldl' (V.zipWith max) v vs
