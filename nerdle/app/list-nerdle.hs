module Main where


import System.Environment
import Text.Read (readMaybe)
import Data.Maybe (listToMaybe)

import Nerdle

main :: IO ()
main = do
    args <- getArgs
    case listToMaybe args >>= readMaybe of
        Nothing -> putStrLn "list-nerdle NUMCHARS"
        Just n  -> mapM_ (putStrLn . printNerdleWord) (enumNerdleWord n)
