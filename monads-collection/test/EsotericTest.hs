module Main(
  main
) where

import Monad.Esoteric
import MonadLaws
import System.Exit

tested :: Bool -> IO ()
tested True = return ()
tested False = exitFailure

main :: IO ()
main =
  do checkMonadIO enumSpan >>= tested
     checkMonadIO enumGold >>= tested
     checkMonadIO enumTwist >>= tested
     checkMonadIO enumNezzle >>= tested
     checkMonadIO enumOdd >>= tested
