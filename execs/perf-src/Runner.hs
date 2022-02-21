{-# LANGUAGE CPP #-}
module Runner(runWork) where

#ifndef INT_TYPE
#define INT_TYPE Int
#endif

import System.Environment (getArgs)
import Control.Exception (evaluate)
import GHC.Stats

runWork :: (INT_TYPE -> Bool) -> IO ()
runWork fn =
  do xStr <- head <$> getArgs
     let x = read xStr
     let yStr = show (fn x)
     evaluate (length yStr)
     putStr $ show x ++ " "
     putStr $ yStr ++ " "
     printStats
{-# NOINLINE runWork #-}

printStats :: IO ()
printStats =
  do cap <- getRTSStatsEnabled
     if cap
       then do s <- getRTSStats
               putStrLn $ unwords [
                     "Alloc=" ++ show (allocated_bytes s),
                     "MaxLive=" ++ show (max_live_bytes s)
                   ]
       else putStrLn "(Stats Disabled)"
