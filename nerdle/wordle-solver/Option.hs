module Option(
  Option(..),
  PlayDiff(..),
  StrategyOpt(..),
  HeuristicOpt(..),

  getOption
) where

import Options.Applicative
import qualified Data.List as List

data Option = PlayMode FilePath PlayDiff | InteractiveMode FilePath HeuristicOpt | AnalyseMode FilePath StrategyOpt

data PlayDiff = Lucky | Fair | Devilish
  deriving (Show, Read, Eq, Ord, Enum, Bounded)

data StrategyOpt = Greedy HeuristicOpt | Complete Int
  deriving Show
data HeuristicOpt = HeightH | InfoH | MinMaxH HeuristicOpt
  deriving Show

getOption :: IO Option
getOption = execParser optParser

optParser :: ParserInfo Option
optParser =
  info
    ( hsubparser
        ( command "play" playParser
          <> command "solver" solverParser
          <> command "analyse" analyseParser
        )
      <**> helper
    )
    mempty

solverParser :: ParserInfo Option
solverParser =
  info
    (InteractiveMode <$> dictArgument <*> heuristic)
    (progDesc "Interactive wordle solver")

playParser :: ParserInfo Option
playParser =
  info
    (PlayMode <$> dictArgument <*> playDifficulty)
    (progDesc "Play against a computer.")

analyseParser :: ParserInfo Option
analyseParser =
  info
    (AnalyseMode <$> dictArgument <*> searchStrategy)
    (progDesc "Make a playbook")

dictArgument :: Parser FilePath
dictArgument = strArgument (metavar "FILE" <> help "Path to the dictionary to use")

heuristic :: Parser HeuristicOpt
heuristic = mkHeuristic <$> depthP <*> htypeP
  where
    htypeP = heightP <|> informationP <|> pure HeightH
    heightP = flag' HeightH (long "height")
    informationP = flag' InfoH (long "info")
    depthP = length <$> many (flag' () (long "minmax"))

    mkHeuristic depth ho
      | depth <= 1 = ho
      | otherwise = MinMaxH $ mkHeuristic (depth - 1) ho

playDifficulty :: Parser PlayDiff
playDifficulty =
  option auto $
    long "difficulty" <> short 'd'
      <> metavar "DIFF"
      <> help ("How much is the computer adversarial. DIFF = " ++ showChoice [minBound .. maxBound :: PlayDiff])
      <> value Fair
      <> showDefault

showChoice :: Show a => [a] -> String
showChoice = List.intercalate "|" . map show

searchStrategy :: Parser StrategyOpt
searchStrategy =
  asum [
    flag' Greedy (long "greedy" <> help "Greedy strategy based on heuristic score")
      <*> heuristic,
    Complete <$> option auto
      (long "complete" <> short 'x' <> metavar "DEPTH" <> help "Exhaust game tree up to DEPTH") 
  ]
