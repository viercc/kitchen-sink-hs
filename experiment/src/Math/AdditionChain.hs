module Math.AdditionChain where

import Data.Ord (comparing)
import Data.List (sortBy)
import Data.Bits

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Chain = IntMap (Int, Int)

isValidChain :: Chain -> Bool
isValidChain chain = IntMap.foldrWithKey step True chain
  where
    live a = a == 1 || IntMap.member a chain
    step key (a,b) validRest = key == a + b && live a && live b && validRest

printChain :: Chain -> IO ()
printChain chain =
  mapM_ step (IntMap.toAscList chain)
  where
    step (a,(b,c)) = putStrLn $ show a ++ " = " ++ show b ++ " + " ++ show c

sampleChain :: Chain
sampleChain = IntMap.fromList
  [ (2,(1,1))
  , (3,(2,1))
  , (6,(3,3))
  , (9,(6,3))
  , (15,(6,9))
  ]

data SolveState = SolveState
  {
    stateTarget :: IntSet
  , stateKnown  :: IntMap (Int, Int)
  }
  deriving (Show)

isCompleted :: SolveState -> Bool
isCompleted state = IntSet.null (stateTarget state)

newtype Dep = Dep { unDep :: IntSet }
  deriving (Show, Eq)

instance Ord Dep where
  compare = comparing (IntSet.size . unDep) <>
            comparing unDep

solveStep :: SolveState -> [SolveState]
solveStep (SolveState target known) =
  case IntSet.maxView target of
    Nothing -> error "step called on completed state"
    Just (x, target') ->
      case immediately x of
        [] -> do ((i,j), Dep newDeps) <- sortBy (comparing snd) $ do
                   i <- [1 .. x `div` 2]
                   let j = x - i
                       newDeps = IntSet.fromList [i,j] IntSet.\\ usables
                   return ((i,j), Dep newDeps)
                 let target'' = target' `IntSet.union` newDeps
                     known'' = IntMap.insert x (i,j) known
                 return $ SolveState target'' known''
        (i,j):_ -> [SolveState target' (IntMap.insert x (i,j) known)]
  where
    usables = IntSet.insert 1 $ IntSet.union target (IntMap.keysSet known)
    immediately x =
      let us = takeWhile (<= x `div` 2) (IntSet.toAscList usables)
      in [ (i,j) | i <- us
                 , let j = x - i
                 , IntSet.member j usables ]

upperBound :: IntSet -> Int
upperBound target =
  let x = IntSet.foldl' (.|.) 0 target
  in logBase2 x + popCount x
  where
    logBase2 x = finiteBitSize x - 1 - countLeadingZeros x

lowerBound :: SolveState -> Int
lowerBound (SolveState target known) = IntSet.size target + IntMap.size known

solve :: IntSet -> [Chain]
solve target =
  go (upperBound target') [SolveState target' IntMap.empty]
  where
    target' = IntSet.delete 1 target
    
    go _  [] = []
    go ub (s:rest)
      | isCompleted s =
          let chain = stateKnown s
              len = IntMap.size chain
          in if ub > len
               then chain : go len rest
               else go ub rest
      | lowerBound s >= ub = go ub rest
      | otherwise = go ub (solveStep s ++ rest)
