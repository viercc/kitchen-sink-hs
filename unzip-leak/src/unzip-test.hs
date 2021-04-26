{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE CPP #-}
module Main(main) where

import Common
import Data.List(unzip)

f :: ([Vec], [Int]) -> (Int, Int)
f (as, bs) = (vecMax $ sumVec as, bs !! 10)

unzipFunctor :: Functor f => f (a,b) -> (f a, f b)
unzipFunctor fab = (fst <$> fab, snd <$> fab)

unzipList :: [(a,b)] -> ([a], [b])
unzipList = unzip

main :: IO ()
main = do
  let (x,y) = f $ UNZIP_FUNCTION $ take 10_000 $ setup 10_000
  print x
  print y
