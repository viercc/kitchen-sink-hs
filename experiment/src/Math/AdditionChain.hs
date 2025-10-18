{-# LANGUAGE PatternSynonyms #-}

module Math.AdditionChain where

import Data.Foldable (toList)

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Sequence (Seq(..))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import qualified Data.Vector.Unboxed as UV
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty (..))

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

powersWithChain :: Semigroup s => Chain -> s -> IntMap s
powersWithChain chain x = loop (IntMap.singleton 1 x) (IntMap.toList chain)
  where
    loop register [] = register
    loop register ((n, (i,j)):rest) =
      let xn = (register IntMap.! i) <> register IntMap.! j
          register' = IntMap.insert n xn register
      in loop register' rest

-- Reconstruct an addition chain from set of its members
reconstruct :: IntSet -> Chain
reconstruct = loop (IntSet.singleton 1) IntMap.empty . IntSet.toAscList
  where
    loop _ acc [] = acc
    loop known acc (x:xs)
      | x <= 0 = error $ "not a positive integer: " ++ show x
      | x == 1 = loop known acc xs
      | otherwise = case findAddition x known of
          Nothing -> error $ "cannot form an addition for " ++ show x ++ " from " ++ show (IntSet.toList known)
          Just (y,z) -> loop (IntSet.insert x known) (IntMap.insert x (y,z) acc) xs

-- | @findAddition n xs@ finds a pair of positive integers @(y,z)@
--   which sums to @n@ from elements of @xs@.
findAddition :: Int -> IntSet -> Maybe (Int, Int)
findAddition n xs = case IntSet.splitMember mid xs of
  (lo, True, hi) -> loop (mid : IntSet.toDescList lo) (mid : IntSet.toAscList hi)
  (lo, False, hi) -> loop (IntSet.toDescList lo) (IntSet.toAscList hi)
  where
    mid = n `div` 2
    loop [] _ = Nothing
    loop _ [] = Nothing
    loop (y:ys) (z:zs) = case compare (y + z) n of
      LT -> loop (y:ys) zs
      EQ -> Just (y,z)
      GT -> loop ys (z:zs)

data SolveState = SolveState
  {
    stateTarget :: IntSet
  , stateKnown  :: IntSet
  }
  deriving (Show)

isCompleted :: SolveState -> Bool
isCompleted state = IntSet.null (stateTarget state)

-- | Greedy algorithm
greedy :: IntSet -> Chain
greedy target0 = reconstruct $ loop initialState
  where
    initialState = SolveState target0 IntSet.empty
    loop state
      | isCompleted state = stateKnown state
      | otherwise = loop (greedyStep state)

greedyStep :: SolveState -> SolveState
greedyStep (SolveState target known) = SolveState target'' known'
  where
    (n,target') = IntSet.deleteFindMax target
    knownSmaller = IntSet.takeWhileAntitone (< n) known
    usables = IntSet.insert 1 $ IntSet.union knownSmaller target'

    mid = n `div` 2
    dep = case findAddition n usables of
      -- If n is a sum of already-available numbers:
      Just _ -> IntSet.empty
      -- If not, find a single new number to require.
      -- Among such numbers, it picks smallest one.
      Nothing -> case IntSet.findMax usables of
        -- Let j be the maximum "usable" number.
        -- If (n == 2*mid) and (j < mid), requiring mid to have
        -- (n = mid + mid) is the smallest.
        -- Otherwise, requiring n - j and have (n = j + (n - j))
        -- is the smallest.
        j | j < mid, even n -> IntSet.singleton mid
          | otherwise       -> IntSet.singleton (n - j)
    
    target'' = IntSet.union target' dep
    known' = IntSet.insert n known

-- | Full algorithm

-- Set of zero, one, or two integers.
-- 
-- Represents new required numbers to have
-- @x = y + z@ in the addition chain.
data Dep = Dep0 | Dep1 !Int | Dep2 !Int !Int
  deriving (Show, Eq, Ord)

-- Dep from a list. If the list have more than 2
-- elements, these extra elements are discarded.
makeDep :: [Int] -> Dep
makeDep xs = case xs of
  [] -> Dep0
  [x] -> Dep1 x
  (x:y:_) -> case compare x y of
    LT -> Dep2 x y
    EQ -> Dep1 x
    GT -> Dep2 y x

depToSet :: Dep -> IntSet
depToSet dep = case dep of
  Dep0 -> IntSet.empty
  Dep1 i -> IntSet.singleton i
  Dep2 i j -> IntSet.fromDistinctAscList [i,j]

sortuniq :: Ord k => [k] -> [k]
sortuniq = Set.toAscList . Set.fromList

solveStep :: SolveState -> [SolveState]
solveStep (SolveState target known) =
  case IntSet.maxView target of
    Nothing -> error "step called on completed state"
    Just (x, target') ->
      case sortuniq (genDeps x target') of
        -- There is a "both known" case
        Dep0 : _ -> [SolveState target' (IntSet.insert x known)]
        -- There aren't such one
        deps -> do
          dep <- deps
          let target'' = target' `IntSet.union` depToSet dep
              known'' = IntSet.insert x known
          pure $ SolveState target'' known''
  where
    genDeps x target' = do
      -- Available numbers
      let usables = IntSet.union target' (IntSet.insert 1 known)
      -- Generate (i,j) such that (1 <= i <= j), (i + j == x)
      i <- [1 .. x `div` 2]
      let j = x - i
      pure $ makeDep $ filter (`IntSet.notMember` usables) [i,j]

solve :: IntSet -> Chain
solve target =
  reconstruct $ go greedySolution [state0]
  where
    target' = IntSet.delete 1 target
    greedySolution = IntMap.keysSet $ greedy target'
    state0 = SolveState target' IntSet.empty
    
    go best [] = best
    go best (s:rest)
      | isCompleted s =
          let chain = stateKnown s
          in if ub > IntSet.size chain
               then go chain rest
               else go best rest
      | lowerBound s >= ub = go best rest
      | otherwise = go best (solveStep s ++ rest)
      where
        ub = IntSet.size best
    
    lowerBound :: SolveState -> Int
    lowerBound (SolveState t k) = IntSet.size t + IntSet.size k

-- | Knuth's power tree
--
-- (as a map to parent integer in the tree)
newtype PowerTree = MkPowerTree (UV.Vector Int)
  deriving (Show, Eq)

pathToRoot :: PowerTree -> Int -> [Int]
pathToRoot (MkPowerTree table) = go
  where
    go n
      | n == 1 = [1]
      | otherwise = case table UV.!? (n - 2) of
          Nothing -> []
          Just n' -> n : go n'

reconstructChain :: PowerTree -> Int -> Chain
reconstructChain kpt n = reconstruct $ IntSet.fromList $ pathToRoot kpt n

buildKPTUpTo :: Int -> PowerTree
buildKPTUpTo nMax = toPowerTree $ go IntMap.empty (Seq.singleton 1)
  where
    go :: IntMap (NonEmpty Int) -> Seq Int -> IntMap (NonEmpty Int)
    go kpt Empty = kpt
    go kpt (n :<| rest) = go kpt' (rest <> Seq.fromList (IntSet.toAscList children))
      where
        path = maybe [] toList (IntMap.lookup n kpt)
        path' = n :| path
        known = IntMap.keysSet kpt
        children = IntSet.fromList [ n + k | k <- toList path', n + k <= nMax ] IntSet.\\ known
        kpt' = IntMap.union kpt (IntMap.fromSet (const path') children)

    toPowerTree kpt = MkPowerTree $ UV.generate (nMax - 1) f
      where
        f i = NonEmpty.head (kpt IntMap.! (i + 2))

main :: IO ()
main = do
  putStrLn "n,l(n),l_greedy(n),l_knuth(n)"
  mapM_ printComparison [2 .. nMax]
  where
    nMax = 128
    trueShortest n = IntMap.size $ solve (IntSet.singleton n)
    greedyLen n = IntMap.size $ greedy (IntSet.singleton n)
    kpt = buildKPTUpTo 128
    knuthLen n = length (pathToRoot kpt n) - 1

    printComparison n = do
      putStrLn $
        show n ++ ", " ++
        show (trueShortest n) ++", " ++
        show (greedyLen n) ++ ", " ++
        show (knuthLen n)
