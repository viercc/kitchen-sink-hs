#!/usr/bin/env cabal
{- cabal:
build-depends: base
ghc-options:   -O0 -threaded -rtsopts
-}
-- If it is built with optimization by removing -O0 from the
-- above line, it won't work
import Control.Concurrent
import Data.IORef

main :: IO ()
main = main1

main1 :: IO ()
main1 =
  do x <- newMVar False
     putStrLn "A"
     forkIO $ do
       putStrLn "B"
       threadDelay 10000
       putStrLn "C"
       _ <- takeMVar x
       putMVar x True
     loop x
  where
    loop x =
      do done <- takeMVar x
         putMVar x False
         if done then return ()
                 else loop x

-- Do work
main2 :: IO ()
main2 =
  do x <- newIORef False
     putStrLn "A"
     forkIO $ do
       putStrLn "B"
       threadDelay 10000
       putStrLn "C"
       atomicWriteIORef x True
     loop x
  where
    loop x =
      do done <- atomicModifyIORef' x (\b -> (b, b))
         if done then return ()
                 else loop x
