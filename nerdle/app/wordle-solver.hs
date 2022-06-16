{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Prelude hiding (Word)
import Control.Monad (forever)
import Data.Foldable
import Data.List (sortOn)
import Data.Ord (comparing)

import System.IO
import System.Environment (getArgs)

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map
import qualified Data.Vector as V

import Collection
import WordleLike ( Response(..) )
import WordleAppCommons

data Option = HelpMode | InitMode FilePath FilePath | InteractiveMode FilePath | PlayMode FilePath

getOption :: IO Option
getOption =
    do (opt, rest) <- parseArgs <$> getArgs
       if null rest
         then return ()
         else putStrLn $ "Warning: unnecessary args = " ++ show rest
       return opt

parseArgs :: [String] -> (Option, [String])
parseArgs args = case args of
    "--help" : rest -> (HelpMode, rest)
    "--init" : inFile : outFile : rest -> (InitMode inFile outFile, rest)
    "--solver" : inFile : rest -> (InteractiveMode inFile, rest)
    "--play" : inFile : rest -> (PlayMode inFile, rest)
    rest -> (HelpMode, rest)

readWordListFileWithMsg :: FilePath -> IO (V.Vector Word)
readWordListFileWithMsg inFile = do
    ws <- readWordListFile inFile
    let n = length ws
    putStrLn $ "Read " ++ show inFile ++ ": " ++ show n ++ " words loaded"
    pure $ V.fromList ws

main :: IO ()
main = do
    opt <- getOption
    case opt of
        HelpMode -> printHelp
        InitMode inFile outFile -> initMode inFile outFile
        InteractiveMode inFile -> interactiveMode inFile
        PlayMode inFile -> playMode inFile

printHelp :: IO ()
printHelp = putStrLn $
    "Usage: wordle-solver\n" ++
    "\t--help\n" ++
    "\t--init inFile outFile\n" ++
    "\t--solver inFile\n" ++
    "\t--play inFile\n"

initMode :: FilePath -> FilePath -> IO ()
initMode inFile outFile = do
    putStrLn "Sorting the word list by heuristic (better -> worse)"
    putStrLn "This will take a time..."
    ws <- readWordListFileWithMsg inFile
    let ws' = withCollection ws sortByHeuristic
    withFile outFile WriteMode $ \out ->
        for_ ws' $ \w -> hPutStrLn out (toList w)

sortByHeuristic :: Collection Word i => Set i -> [Word]
sortByHeuristic coll = map itemValue $ sortOn (\x -> fst (maxSizeScore x coll)) $ Set.toList universe

interactiveMode :: FilePath -> IO ()
interactiveMode inFile = do
    ws <- readWordListFileWithMsg inFile
    withCollection ws interactiveMain

interactiveMain :: (Collection Word i) => Set i -> IO ()
interactiveMain coll = forever wizard
  where
    initialRecommend = Set.findMin coll
    
    wizard = do
        describeCandidates coll
        putStrLn $ "Recommend: " ++ show (itemValue initialRecommend)
        i <- askQuery
        let nexts = outcomes i coll
        s <- askResp nexts
        loop s

    loop s = do
        describeCandidates s
        let (recommend, nexts) = minmaxSizeStrategy s
        if Map.null nexts
          then putStrLn $ "Answer: " ++ show (itemValue recommend)
          else do
            putStrLn $ "Recommend: " ++ show (itemValue recommend)
            i <- askQuery
            if i == recommend
              then do s' <- askResp nexts
                      loop s'
              else do s' <- askResp (outcomes i s)
                      loop s'
    
    revWordMap = Map.fromList [ (itemValue i, i) | i <- Set.toList coll ]
    askQuery = promptMap "Enter the query> " (Just . V.fromList) revWordMap
    askResp = promptMap "Enter the response ([Miss,Blow,Hit] = [-,+,#] resp.)> " readResp

    describeCandidates s
      | Set.size s <= 5 = putStrLn numMsg >>
                          for_ s (print . itemValue)
      | otherwise       = putStrLn numMsg
      where numMsg = show (Set.size s) ++ " candidates remaining:"

playMode :: FilePath -> IO ()
playMode inFile = do
    ws <- readWordListFileWithMsg inFile
    withCollection ws playMain

playMain :: (Collection Word i) => Set i -> IO ()
playMain coll = forever wizard
  where
    wizard = do
        putStrLn "Let's play with bot!"
        loop coll

    loop s = do
        putStrLn $ show (Set.size s) ++ " words remaining"
        i <- askQuery
        let nexts = outcomes i s
            (resp, s') = maximumBy (comparing (Set.size . snd)) (Map.toList nexts)
        putStrLn $ "|@@|  " ++ V.toList (itemValue i) ++ "  |@@|"
        putStrLn $ "|@@|  " ++ printResp resp         ++ "  |@@|"
        if all (== Hit) resp
          then putStrLn "Good job!"
          else loop s'
    
    revWordMap = Map.fromList [ (itemValue i, i) | i <- Set.toList coll ]
    askQuery = promptMap "Enter the query> " (Just . V.fromList) revWordMap
