{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Prelude hiding (Word)
import Control.Monad (forever)
import Data.Foldable
import Data.List (mapAccumL)

import System.IO
import System.Exit (exitFailure)

import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import qualified Data.Vector as V

import System.Random.Stateful

import WordleLike

import Search
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Option

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
        InteractiveMode inFile h -> interactiveMode inFile h
        PlayMode inFile difficulty -> playMode inFile difficulty
        AnalyseMode inFile stratOpt -> analyseMode inFile stratOpt

interactiveMode :: FilePath -> HeuristicOpt -> IO ()
interactiveMode inFile h = do
    ws <- readWordListFileWithMsg inFile
    interactiveMain ws h

data SolverCommand a = SolverRecommend | SolverUndo | SolverReset | SolverQuery a

readCmd :: (String -> Either String a) -> String -> Either String (SolverCommand a)
readCmd reader s = case reader s of
    Left errMsg -> case s of
        "/recommend" -> Right SolverRecommend
        "/undo" -> Right SolverUndo
        "/reset" -> Right SolverReset
        _ -> Left errMsg
    Right a -> Right (SolverQuery a)

interactiveMain :: V.Vector Word -> HeuristicOpt -> IO ()
interactiveMain dict h = banner >> forever wizard
  where
    allIxes = [0 .. V.length dict - 1]
    wholeGame = wordleToAbstract dict

    banner = do
        putStrLn "Follow the wizard to solve a puzzle."
        putStrLn "Input responses in the following form:"
        putStrLn "  Hit: \'#\',  Blow: \'?\', Miss: \'.\'"
        putStrLn "E.g. To enter Miss-Miss-Hit-Blow-Miss response, input ..#?."
        putStrLn ""
        putStrLn "Command: /recommend to get a recommended input"
        putStrLn "         /undo to go back to the previous turn"
        putStrLn "         /reset to return to the beginning"

    wizard = loop (Set.fromDistinctAscList allIxes) []
    
    loop s undoStack
      | Set.size s <= 1 = putStrLn $ "Answer Found: " ++ showWord (Set.findMin s)
      | otherwise = describeCandidates s >> queryStep
      where 
        queryStep = do
          iCmd <- askQuery
          case iCmd of
            SolverRecommend -> printRecommend s >> loop s undoStack
            SolverUndo -> undo undoStack
            SolverReset -> reset
            SolverQuery i -> respStep i
        respStep i = do
          respCmd <- askResp
          case respCmd of
            SolverRecommend -> putStrLn "Use /recommend when prompted to input query" >> respStep i
            SolverUndo -> undo undoStack
            SolverReset -> reset
            SolverQuery r -> do
                let s' = Set.filter (\j -> response (dict V.! j) (dict V.! i) == r) s
                if Set.size s' == 0
                    then putStrLn "No possible answers satisfy it. Misinput or wrong dictionary?" >> respStep i
                    else loop s' (s : undoStack)
    
    reset = putStrLn "Return to the start of the game..." >> wizard
    undo []              = reset
    undo (sr:undoStack') = putStrLn "Return to the previous turn..." >> loop sr undoStack'

    showWord i = show (dict V.! i)
    revWordMap = revmap dict
    askQuery = promptInteract "Enter the query >>>> " (readCmd $ readByMap (Just . V.fromList) revWordMap)
    askResp  = promptInteract "Enter the response > " (readCmd readResponseWithErr)
    readResponseWithErr str = case readResponse str of
        Nothing -> Left $ "Parse failure: " ++ show str
        Just a -> Right a

    heuristicFun = makeHeuristic h
    printRecommend s = putStrLn $ "Recommend: " ++ showWord (recommend s)
    recommend s
      | Set.size s <= 10 = stratMove (perfectStrategy 1 game)
      | otherwise = stratMove (heuristicStrategy heuristicFun game)
      where
        game = restrictGame wholeGame (IntSet.fromDistinctAscList . Set.toList $ s)

    describeCandidates s
      | Set.size s <= 5 = putStrLn numMsg >>
                          for_ s (print . (dict V.!))
      | otherwise       = putStrLn numMsg
      where numMsg = show (Set.size s) ++ " words remaining"

playMode :: FilePath -> PlayDiff -> IO ()
playMode inFile diff = do
    ws <- readWordListFileWithMsg inFile
    playMain diff ws

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

outcomes :: V.Vector Word -> Int -> IntSet -> Map Response IntSet
outcomes dict x ys = Map.fromListWith IntSet.union
    [ (response (dict V.! y) (dict V.! x), IntSet.singleton y) | y <- IntSet.toList ys ]

playMain :: PlayDiff -> V.Vector Word -> IO ()
playMain diff dict = forever wizard
  where
    allIxes = IntSet.fromDistinctAscList [0 .. V.length dict - 1]
    wizard = do
        putStrLn "Let's play with bot!"
        loop allIxes

    loop s = do
        putStrLn $ show (IntSet.size s) ++ " words remaining"
        i <- askQuery
        let nexts = outcomes dict i s
        (resp, s') <- chooser i nexts
        putStrLn $ "|@@|  " ++ V.toList (dict V.! i) ++ "  |@@|"
        putStrLn $ "|@@|  " ++ showResponse resp     ++ "  |@@|"
        if all (== Hit) resp
          then putStrLn "Good job!"
          else loop s'
    
    chooser x = case diff of
        Lucky -> sampleFromMap
        Fair -> weightedChooser normalWeigh
        Devilish -> weightedChooser (devilsWeigh x)
    
    weightedChooser weigh nexts
        | Map.size nexts == 0 = error "impossible?"
        | Map.size nexts == 1 = pure $ Map.findMin nexts
        | otherwise           = sampleWeighted weigh (Map.toList nexts)
    normalWeigh (_,s) = IntSet.size s
    devilsWeigh x (_,s) | s == IntSet.singleton x = 0
                        | otherwise               = IntSet.size s ^ (3 :: Int)
    
    revWordMap = revmap dict
    askQuery = promptMap "Enter the query> " (Just . V.fromList) revWordMap

analyseMode :: FilePath -> StrategyOpt -> IO ()
analyseMode inFile strat = do
    ws <- readWordListFileWithMsg inFile
    analyseMain ws strat

makeHeuristic :: HeuristicOpt -> Heuristic
makeHeuristic sopt = case sopt of
    MinMaxH sopt' -> minmaxHeuristic (makeHeuristic sopt')
    HeightH -> heightHeuristic
    InfoH -> informationHeuristic

analyseMain :: V.Vector Word -> StrategyOpt -> IO ()
analyseMain dict stratName = do
    putStrLn $ "strategy = " ++ show stratName
    maybe noStrat (prettyTree 0 "") $ case stratName of
        Greedy h -> Just $ heuristicStrategy (makeHeuristic h) game
        Complete n -> winningStrategyIn n game
  where
    game = wordleToAbstract dict
    
    noStrat = putStrLn "No strategy found"
    prettyTree d prefix str =
      do let (x0, children) = interpretStrategy dict game str
         putStrLn $ ">" ++ indent d ++ prefix ++ V.toList x0
         prettyChildren (d+1) children
    
    prettyChildren d children =
        for_ (Map.toList children) $ \(r, s) -> do
            prettyTree d (showResponse r ++ " → ") s

    indent d = replicate (2*d) ' '

-- * Vector utils

revmap :: Ord a => V.Vector a -> Map a Int
revmap as = Map.fromList [ (a,i) | (i,a) <- V.toList (V.indexed as)]