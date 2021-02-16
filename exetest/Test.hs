module Main(main) where

import System.Exit
import System.Process

main :: IO ()
main = do
  out <- readCreateProcess (proc executableName args) ""
  if out == expectedOut
    then exitSuccess
    else do putStrLn $ "expected: " ++ show expectedOut
            putStrLn $ "actual:   " ++ show out
            exitFailure

executableName :: String
executableName = "subject"

args :: [String]
args = ["foo", "bar bar", "baz\nbaz"]

expectedOut :: String
expectedOut = "1: foo\n2: bar bar\n3: baz\nbaz\n"
