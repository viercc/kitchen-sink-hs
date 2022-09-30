{-# LANGUAGE TypeApplications #-}
module Main where


import System.Environment
import System.Exit

import Text.Read (readMaybe)

import Nerdle
import Digit

data Option = Option { numChars :: Int, radixMode :: NerdleRadix }

data NerdleRadix = DecimalNerdle | BinaryNerdle

parseArgs :: [String] -> IO Option
parseArgs [] = helpAndExit
parseArgs (numCharsArg : rest) = case readMaybe numCharsArg of
    Nothing -> helpAndExit
    Just n -> case rest of
        [] -> pure Option { numChars = n, radixMode = DecimalNerdle }
        ["--decimal"] -> pure Option { numChars = n, radixMode = DecimalNerdle }
        ["--binary"] -> pure Option { numChars = n, radixMode = BinaryNerdle }
        _ -> helpAndExit

helpAndExit :: IO a
helpAndExit = putStrLn "Usage: list-nerdle NUMCHARS [--decimal | --binary]" >> exitFailure

main :: IO ()
main = do
    opt <- getArgs >>= parseArgs
    case radixMode opt of
        DecimalNerdle -> mapM_ (putStrLn . printNerdleWord) (enumNerdleWord @Dec (numChars opt))
        BinaryNerdle  -> mapM_ (putStrLn . printNerdleWord) (enumNerdleWord @Bit (numChars opt))
