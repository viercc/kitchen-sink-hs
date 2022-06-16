module Main where

import Nerdle

main :: IO ()
main = mapM_ (putStrLn . printNerdleWord) (enumNerdleWord 8)
