module Main where

import System.IO
import System.Process

main :: IO ()
main = withFile "hello.txt" ReadWriteMode $ \h -> do
    hPutStrLn h "hello"
    hFlush h
    callProcess "bash" ["-c", "echo foo > hello.txt"]
    hSeek h AbsoluteSeek 0
    str <- hGetContents' h
    print str
