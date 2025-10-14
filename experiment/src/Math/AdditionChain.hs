module Math.AdditionChain where

import Data.List (sort)

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

-- (numUnknown, unknown, expr)
type Dep = (Int, [Int], (Int, Int))

solveStep :: SolveState -> [SolveState]
solveStep (SolveState target known) =
  case IntSet.maxView target of
    Nothing -> error "step called on completed state"
    Just (x, target') ->
      case sort (genDeps x target') of
        -- There is a "both known" case
        (0, _, (i,j)) : _ -> [SolveState target' (IntMap.insert x (i,j) known)]
        -- There aren't such one
        deps -> do
          (_,unknowns,(i,j)) <- deps
          let target'' = target' `IntSet.union` IntSet.fromList unknowns
              known'' = IntMap.insert x (i,j) known
          return $ SolveState target'' known''
  where
    genDeps x target' = do
      -- Available numbers without requireing no new dependency
      let usables = IntSet.union target' (IntSet.insert 1 (IntMap.keysSet known))
      -- Generate (i,j) such that (1 <= i <= j), (i + j == x)
      i <- [1 .. x `div` 2]
      let j = x - i
          unknowns = filter (`IntSet.notMember` usables) [j,i]
          numUnknowns
            | i == j = min 1 (length unknowns)
            | otherwise = length unknowns
      pure (numUnknowns, unknowns, (i,j))

greedySolve :: IntSet -> Chain
greedySolve target0 = loop initialState
  where
    initialState = SolveState target0 IntMap.empty
    loop state
      | isCompleted state = stateKnown state
      | otherwise = case solveStep state of
          [] -> error "solveStep must return non-empty!"
          state' : _ -> loop state'

upperBound :: IntSet -> Int
upperBound target = IntMap.size (greedySolve target)

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
