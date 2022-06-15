module Main where

import Nerdle
import V6(V6)

main :: IO ()
main = mapM_ (putStrLn . printNerdleWord) (enumNerdleWord :: [V6 NerdleChar])
