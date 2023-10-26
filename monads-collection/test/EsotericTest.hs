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
     checkMonadIO enumTwist' >>= tested
     tested $ all (\mma -> joinTwist' mma == joinTwist'viaIso mma) (skolem2 enumTwist')
     checkMonadIO enumNezzle >>= tested
     checkMonadIO enumOdd >>= tested
