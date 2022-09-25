{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Prelude hiding (Word)
import Control.Monad (forever)
import Data.Foldable
import Data.List (sortOn, mapAccumL)

import System.IO
import System.Environment (getArgs)

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map
import qualified Data.Vector as V

import Collection
import WordleLike ( Response(..) )
import WordleAppCommons

import System.Random.Stateful

data Option = HelpMode | InitMode FilePath FilePath | InteractiveMode FilePath | PlayMode FilePath PlayDiff | AnalyseMode FilePath

data PlayDiff = Easy | Normal | Hard

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
    "--play" : inFile : rest -> case rest of
        [] -> (PlayMode inFile Normal, [])
        ("--easy" : rest') -> (PlayMode inFile Easy, rest')
        ("--normal" : rest') -> (PlayMode inFile Normal, rest')
        ("--hard" : rest') -> (PlayMode inFile Hard, rest')
        _ -> (HelpMode, rest)
    "--analyse" : inFile : rest -> (AnalyseMode inFile, rest)
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
        PlayMode inFile difficulty -> playMode inFile difficulty
        AnalyseMode inFile -> analyseMode inFile

printHelp :: IO ()
printHelp = putStrLn $
    "Usage: wordle-solver\n" ++
    "\t--help\n" ++
    "\t--init inFile outFile\n" ++
    "\t--solver inFile\n" ++
    "\t--play inFile [--easy | --normal | --hard]    (default: --normal) \n" ++
    "\t--analyse inFile\n"

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
    askResp = promptMap "Enter the response ([Miss,Blow,Hit] = [.,?,#] resp.)> " readResp

    describeCandidates s
      | Set.size s <= 5 = putStrLn numMsg >>
                          for_ s (print . itemValue)
      | otherwise       = putStrLn numMsg
      where numMsg = show (Set.size s) ++ " candidates remaining:"

playMode :: FilePath -> PlayDiff -> IO ()
playMode inFile diff = do
    ws <- readWordListFileWithMsg inFile
    withCollection ws (playMain diff)

sampleFromMap :: Map.Map k a -> IO (k, a)
sampleFromMap m = do
    i <- applyAtomicGen (randomR (0, Map.size m - 1)) globalStdGen
    pure $ Map.elemAt i m

cumsum :: Num a => [a] -> (a, [a])
cumsum = mapAccumL (\s x -> let s' = s + x in s' `seq` (s', s')) 0

sampleWeighted :: (x -> Int) -> [x] -> IO x
sampleWeighted weigh xs = do
    k <- applyAtomicGen (randomR (0, totalWeight - 1)) globalStdGen
    case Map.lookupGT k table of
        Nothing -> error "impossible?"
        Just (_,x) -> pure x
    where
      (totalWeight, ws) = cumsum (weigh <$> xs)
      table = Map.fromList (zip ws xs)

playMain :: (Collection Word i) => PlayDiff -> Set i -> IO ()
playMain diff coll = forever wizard
  where
    wizard = do
        putStrLn "Let's play with bot!"
        loop coll
    
    loop s = do
        putStrLn $ show (Set.size s) ++ " words remaining"
        i <- askQuery
        let nexts = outcomes i s
        (resp, s') <- chooser i nexts
        putStrLn $ "|@@|  " ++ V.toList (itemValue i) ++ "  |@@|"
        putStrLn $ "|@@|  " ++ printResp resp         ++ "  |@@|"
        if all (== Hit) resp
          then putStrLn "Good job!"
          else loop s'
    
    chooser x = case diff of
        Easy -> sampleFromMap
        Normal -> weightedChooser normalWeigh
        Hard -> weightedChooser (devilsWeigh x)
    
    weightedChooser weigh nexts
        | Map.size nexts == 0 = error "impossible?"
        | Map.size nexts == 1 = pure $ Map.findMin nexts
        | otherwise           = sampleWeighted weigh (Map.toList nexts)
    normalWeigh (_,s) = Set.size s
    devilsWeigh x (_,s) | s == Set.singleton x = 0
                        | otherwise            = Set.size s ^ (3 :: Int)
    
    revWordMap = Map.fromList [ (itemValue i, i) | i <- Set.toList coll ]
    askQuery = promptMap "Enter the query> " (Just . V.fromList) revWordMap

analyseMode :: FilePath -> IO ()
analyseMode inFile = do
    ws <- readWordListFileWithMsg inFile
    withCollection ws analyseMain

analyseMain :: Collection Word i => Set i -> IO ()
analyseMain allWords = putStrLn . ppr $ gameTree
  where
    ppr = prettyPrintGameTree (V.toList . itemValue) printResp
    allGameTree = completeGame allWords
    
    gameTree = pruneContinues $ winsInNTurns 3 $ Continues <$ allGameTree