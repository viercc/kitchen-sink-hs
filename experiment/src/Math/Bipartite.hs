{-# LANGUAGE BlockArguments #-}
module Math.Bipartite where

import Data.List (foldl')

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Math.Combinatorics (partitions)
import Data.Equivalence.Monad
import Data.Foldable (for_)
import Control.Monad (guard)

data Edge = E !Int !Int
    deriving (Show, Eq, Ord)

type Graph = Set.Set Edge

genBipartite :: [Int] -> [Int] -> [Graph]
genBipartite ordA ordB
  | sum ordA /= sum ordB = error "Total number of edges differ!"
  | otherwise = map mkGraph $ go (zip [0..] ordA) initialCapacity
  where
    initialCapacity = Map.fromList [ (v,w) | (v,w) <- zip [0..] ordB, w > 0 ]
    go [] _ = [[]]
    go ((a,na) : as) capacity = do
      bs <- chooseFrom na (Map.keys capacity)
      let capacity' = foldl' deleteItem capacity bs
      rest <- go as capacity'
      pure $ (E a <$> bs) ++ rest
    mkGraph = Set.fromList

transposeA, transposeB :: Int -> Graph -> Graph
transposeA i = Set.map f
  where
    f (E a b)
      | a == i     = E (i + 1) b
      | a == i + 1 = E i b
      | otherwise  = E a b
transposeB i = Set.map f
  where
    f (E a b)
      | b == i     = E a (i + 1)
      | b == i + 1 = E a i
      | otherwise  = E a b

genUniqueBipartite :: [Int] -> [Int] -> [Graph]
genUniqueBipartite ordA ordB = uniqueUpTo isos (genBipartite ordA ordB)
  where
    isos = (transposeA <$> swapAs) ++
           (transposeB <$> swapBs)
    swapAs = [ i | (i, n, n') <- zip3 [0..] ordA (tail ordA), n == n' ]
    swapBs = [ i | (i, n, n') <- zip3 [0..] ordB (tail ordB), n == n' ]

findNontrivial :: [ (Int, [Int], [Int], Int) ]
findNontrivial = do
  n <- [1 ..]
  let orders = partitions n
      orderPairs = [ [x,x] | x <- orders ] ++ chooseFrom 2 orders
  [ordA, ordB] <- orderPairs
  let result = length $ genUniqueBipartite ordA ordB
  guard (result >= 2)
  pure (n, ordA, ordB, result)

----

chooseFrom :: Int -> [a] -> [[a]]
chooseFrom n as
  | n < 0 = error "Negative?"
  | n > m = []
  | otherwise = chooseFrom' n m as
  where
    m = length as

chooseFrom' :: Int -> Int -> [a] -> [[a]]
chooseFrom' n m as
  | n == 0 = [[]]
  | n == m = [as]
  | otherwise = case as of
      [] -> []
      a : as' -> ((a :) <$> chooseFrom' (n - 1) (m - 1) as') ++ chooseFrom' n (m - 1) as'

deleteItem :: Ord k => Map.Map k Int -> k -> Map.Map k Int
deleteItem bag k = Map.update (\n -> if n <= 1 then Nothing else Just (n - 1)) k bag

uniqueUpTo :: Ord a => [a -> a] -> [a] -> [a]
uniqueUpTo isoGenerators as = runEquivM id min do
  for_ as $ \a -> equateAll (a : map ($ a) isoGenerators)
  classes >>= traverse desc

graphToDot :: Graph -> String
graphToDot g = unlines $ ["digraph {"] ++ map indent contents ++ ["}"]
  where
    indent = ("  " ++)
    contents = nodeContents ++ edgeContents
    uNodes = Set.toList $ Set.fromList [ u | E u _ <- Set.toList g ]
    vNodes = Set.toList $ Set.fromList [ v | E _ v <- Set.toList g ]
    nodeContents = map (mkNodeStmt "a") uNodes ++ map (mkNodeStmt "b") vNodes
    mkNodeStmt prefix nodeId = prefix ++ show nodeId ++ "[label=\"\"];"
    edgeContents = map mkEdge (Set.toList g)
    mkEdge (E u v) = "a" ++ show u ++ " -> " ++ "b" ++ show v ++ ";"

main :: IO ()
main = do
  mapM_ print $ take 40 findNontrivial