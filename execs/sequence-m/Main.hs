{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE BangPatterns #-}
module Main(main) where

import Control.Monad (replicateM)
import Data.IORef
import GHC.Clock (getMonotonicTimeNSec)
import Data.Word (Word64)

nanoSecToSec :: Word64 -> Double
nanoSecToSec t = fromRational $ toRational t / 1E9

measure :: IO () -> IO ()
measure m = do
    t0 <- getMonotonicTimeNSec
    m
    t1 <- getMonotonicTimeNSec
    print $ nanoSecToSec (t1 - t0)

main :: IO ()
main = do
    ref <- newIORef (1 :: Int)
    let p = modifyIORef' ref negate >> readIORef ref
    measure $ do
        bs <- revreplicateM n p
        print (sum bs)
    measure $ do
        as <- replicateM n p
        print (sum as)
  where
    n = 20_000_000

revreplicateM :: Monad m => Int -> m a -> m [a]
revreplicateM n ma = go n []
  where
    go !n acc
      | n <= 0    = pure acc
      | otherwise = ma >>= \a -> go (n - 1) (a : acc)