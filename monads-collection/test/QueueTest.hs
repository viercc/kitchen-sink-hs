module Main(
  main
) where

import Monad.Queue

example1 :: Queue Char ()
example1 = do
  offer "abcde"
  ab <- poll 2
  cd <- poll 2
  offer cd
  offer ab
  poll 5
  return ()

example2 :: Int -> Queue Char ()
example2 n | n <= 0    = return ()
           | otherwise = example1 >> example2 (n-1)

-- | This example should run in O(1) memory consumption.
--   This package compiles this test executable with
--
--       @-rtsopts -with-rtsopts=-M2m@
--   
--   to confirm it.
main :: IO ()
main = do
  putStrLn ""
  print $ length $ traceQueue $ example2 1000000
  print $ evalQueue $ example2 1000000
  print $ execQueue $ example2 1000000
