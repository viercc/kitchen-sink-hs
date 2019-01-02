module Main where

import Pipes
import qualified Data.Sequence as S
import Data.Sequence (Seq((:<|), Empty), (><))
import Control.DeepSeq

type Node = Int

getNeighbours :: Node -> IO [Node]
getNeighbours i = return [i+1..i+1001]

allNodes :: S.Seq Node -> Producer Node IO ()
allNodes Empty = return ()
allNodes toVisit@(x :<| xs) = do
  neighbours <- lift $ S.fromList <$> getNeighbours  x
  let newNodesToVisit = xs >< neighbours
  lift . putStrLn $ "LENGTH   " <> show (S.length newNodesToVisit)
  each neighbours
  allNodes newNodesToVisit

startNode = S.singleton 0

main :: IO ()
main = runEffect $ for (allNodes startNode) (\_ -> return ())
