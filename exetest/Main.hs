module Main where

import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  mapM_ putStrLn [ show n ++ ": " ++ arg | (n,arg) <- zip [1..] args ]
