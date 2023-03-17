{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Prelude hiding (Word)
import Control.Monad (forever)
import Data.Foldable
import Data.List (sortOn, mapAccumL)

import System.IO
import System.Environment (getArgs)
import System.Exit (exitFailure)

import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V

import System.Random.Stateful

import Collection
import WordleLike ( Response(..) )

import Types
import Search
import Data.Ord (Down(..))
import Text.Read (readMaybe)

data Option = HelpMode | InitMode FilePath FilePath | InteractiveMode FilePath | PlayMode FilePath PlayDiff | AnalyseMode FilePath AnalysisType

data PlayDiff = Easy | Normal | Hard
  deriving Show
data AnalysisType = Simple | Heuristic !Int | Perfect
  deriving Show

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
    "--analyse" : inFile : rest -> case rest of
        [] -> (AnalyseMode inFile Simple, rest)
        ("--simple" : rest') -> (AnalyseMode inFile Simple, rest')
        ("-h" : rest') -> (AnalyseMode inFile (Heuristic 5), rest')
        ("--heuristic" : heuristicWidth : rest') -> case readMaybe heuristicWidth of
          Just width -> (AnalyseMode inFile (Heuristic width), rest')
          Nothing    -> (HelpMode, rest)
        ("--perfect" : rest') -> (AnalyseMode inFile Perfect, rest')
        _ -> (HelpMode, rest)
    rest -> (HelpMode, rest)

printHelp :: IO ()
printHelp = putStrLn $ unlines [
    "Usage: wordle-solver",
    "\t--help",
    "\t--init inFile outFile",
    "\t--solver inFile",
    "\t--play inFile [--easy | --normal | --hard]",
    "\t\t (default: --normal)",
    "\t--analyse inFile [--simple | -h | --heuristic N | --perfect]",
    "\t\t (default: --simple)",
    "\t\t -h is a shorthand for --heuristic 5"
  ]

readWordListFile :: FilePath -> IO [Word]
readWordListFile fileName = do
    wordTxt <- readFile' fileName
    let ws = map V.fromList $ filter (not . null) (lines wordTxt)
    case ws of
        [] -> hPutStrLn stderr "Empty word list!" >> exitFailure
        w:ws' | all (\v -> length w == length v) ws' -> pure ws
              | otherwise                            -> hPutStrLn stderr "Word length varies!" >> exitFailure

promptInteract :: String -> (String -> Either String a) -> IO a
promptInteract msg reader = loop
  where
    loop =
      do putStr msg
         hFlush stdout
         s <- getLine
         case reader s of
          Left errMsg -> putStrLn errMsg >> loop
          Right a -> pure a

readByMap :: (Ord k) => (String -> Maybe k) -> Map k a -> String -> Either String a
readByMap reader dict s = case reader s of
      Nothing -> Left "No parse (try again)"
      Just k -> case Map.lookup k dict of
          Nothing -> Left "Key not found (try again)"
          Just a  -> Right a

promptMap :: (Ord k) => String -> (String -> Maybe k) -> Map k a -> IO a
promptMap msg reader dict = promptInteract msg (readByMap reader dict)

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
        AnalyseMode inFile analysisType -> analyseMode inFile analysisType

initMode :: FilePath -> FilePath -> IO ()
initMode inFile outFile = do
    putStrLn "Sorting the word list by heuristic (better -> worse)"
    putStrLn "This will take a time..."
    ws <- readWordListFileWithMsg inFile
    let ws' = withCollection ws $ \coll ->
          let sortedItems = sortOn (Down . informationScore) $ Set.toList coll
          in  map itemValue sortedItems
    withFile outFile WriteMode $ \out ->
        for_ ws' $ \w -> hPutStrLn out (toList w)

informationScore :: Collection Word i => i -> Double
informationScore i = negate $ sum [ p * log p | resp <- Map.elems (outcomes i allWords), let p = fromIntegral (Set.size resp) / n ]
  where
    allWords = universe
    n = fromIntegral (Set.size allWords)

interactiveMode :: FilePath -> IO ()
interactiveMode inFile = do
    ws <- readWordListFileWithMsg inFile
    withCollection ws interactiveMain

data SolverCommand a = SolverUndo | SolverReset | SolverQuery a

readCmdByMap :: (Ord k) => (String -> Maybe k) -> Map.Map k a -> String -> Either String (SolverCommand a)
readCmdByMap reader dict s = case readByMap reader dict s of
    Left errMsg -> case s of
        "/undo" -> Right SolverUndo
        "/reset" -> Right SolverReset
        _ -> Left errMsg
    Right a -> Right (SolverQuery a)

interactiveMain :: forall i. (Collection Word i) => Set i -> IO ()
interactiveMain coll = banner >> forever wizard
  where
    initialRecommend = Set.findMin coll
    
    banner = do
        putStrLn "Follow the wizard to solve a puzzle."
        putStrLn "Input responses in the following form:"
        putStrLn "  Hit: \'#\',  Blow: \'?\', Miss: \'.\'"
        putStrLn "E.g. To enter Miss-Miss-Hit-Blow-Miss response, input ..#?."
        putStrLn ""
        putStrLn "Command: /undo to go back to the previous turn"
        putStrLn "         /reset to return to the beginning"

    wizard = loop (coll, initialRecommend) []

    allWords = Set.toList universe :: [i]
    
    loop (s,recommend) undoStack = do
        describeCandidates s
        putStrLn $ "Recommend: " ++ show (itemValue recommend)
        iCmd <- askQuery
        case iCmd of
          SolverUndo -> undo undoStack
          SolverReset -> reset
          SolverQuery i -> do
            respCmd <- askResp (outcomes i s)
            case respCmd of
              SolverUndo -> undo undoStack
              SolverReset -> reset
              SolverQuery s'
                | Set.null s' -> putStrLn "Congrats!"
                | otherwise -> 
                  let (_,recommend') = simplePlay allWords s'
                  in loop (s', recommend') ((s, recommend) : undoStack)
    
    reset = putStrLn "Return to the start of the game..." >> wizard
    undo []              = reset
    undo (sr:undoStack') = putStrLn "Return to the previous turn..." >> loop sr undoStack'

    revWordMap = Map.fromList [ (itemValue i, i) | i <- Set.toList coll ]
    askQuery  = promptInteract "Enter the query >>>> " (readCmdByMap (Just . V.fromList) revWordMap)
    askResp r = promptInteract "Enter the response > " (readCmdByMap readResp r)

    describeCandidates s
      | Set.size s == 1 = putStrLn $ "The answer is " ++ show (itemValue (Set.findMin s))
      | Set.size s <= 5 = putStrLn numMsg >>
                          for_ s (print . itemValue)
      | otherwise       = putStrLn numMsg
      where numMsg = show (Set.size s) ++ " words remaining"

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

analyseMode :: FilePath -> AnalysisType -> IO ()
analyseMode inFile analysisType = do
    ws <- readWordListFileWithMsg inFile
    withCollection ws (analyseMain analysisType)

analyseMain :: forall proxy i. Collection Word i => AnalysisType -> proxy i -> IO ()
analyseMain stratName _ = do
    putStrLn $ show stratName ++ " strategy"
    prettyTree 0 "" strategy
  where
    strategy :: Collection Word i => Strategy i
    strategy = case stratName of
        Simple -> simpleStrategy
        Heuristic w -> heuristicStrategy w
        Perfect -> perfectStrategy
    
    prettyTree d prefix s = case s of
      AlreadyWon -> return ()
      Strategy x children ->
        do putStrLn $ ">" ++ indent d ++ prefix ++ showWordItem x
           prettyChildren (d+1) children
    
    prettyChildren d resps =
        for_ (Map.toList resps) $ \(r, s) -> do
            if all (== Hit) r
                then return ()
                else prettyTree d (printResp r ++ " → ") s

    indent d = replicate (2*d) ' '