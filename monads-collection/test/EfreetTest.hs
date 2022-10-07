module Main
  ( main,
  )
where

import Monad.Efreet
import MonadLaws
import System.Exit

tested :: Bool -> IO ()
tested True = return ()
tested False = exitFailure

main :: IO ()
main =
  do checkMonadIO enumTree >>= tested
