module Main
  ( main,
  )
where

import Monad.Trie
import MonadLaws
import System.Exit

tested :: Bool -> IO ()
tested True = return ()
tested False = exitFailure

main :: IO ()
main =
  do checkMonadIO enumTrie >>= tested
