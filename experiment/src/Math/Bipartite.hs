{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
module Math.Bipartite where

import qualified Data.MultiSet as Bag
import qualified Data.Set as Set

import Math.Combinatorics (partitions, Bag)
import Control.Monad (guard)

import EquivalenceUtil ( uniqueUpToH )
import Data.Hashable ( Hashable )
import GHC.Generics (Generic)
import qualified Data.Foldable as F

data Edge = E !Int !Int
    deriving (Show, Eq, Ord, Generic)

instance Hashable Edge

type Graph = Set.Set Edge

genBipartite :: [Int] -> [Int] -> [Graph]
genBipartite ordA ordB
  | sum ordA /= sum ordB = error "Total number of edges differ!"
  | otherwise = map mkGraph $ go (zip [0..] ordA) initialCapacity
  where
    initialCapacity = Bag.fromOccurList [ (v,w) | (v,w) <- zip [0..] ordB, w > 0 ]
    go [] _ = [[]]
    go ((a,na) : as) capacity = do
      bs <- chooseFrom na (Bag.toSet capacity)
      let capacity' = capacity Bag.\\ Bag.fromList bs
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
genUniqueBipartite ordA ordB = uniqueUpToH isos (genBipartite ordA ordB)
  where
    isos = (transposeA <$> swapAs) ++
           (transposeB <$> swapBs)
    swapAs = swappableIndices ordA
    swapBs = swappableIndices ordB

swappableIndices :: (Eq a) => [a] -> [Int]
swappableIndices [] = []
swappableIndices (a0:as) = [ i | (i, a, a') <- zip3 [0..] (a0:as) as, a == a' ]

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

chooseFrom :: (Foldable t) => Int -> t k -> [[k]]
chooseFrom n as
  | n < 0 = error "Negative?"
  | n > m = []
  | otherwise = chooseFrom' n m (F.toList as)
  where
    m = F.length as

chooseFrom' :: Int -> Int -> [a] -> [[a]]
chooseFrom' n m as
  | n == 0 = [[]]
  | n == m = [as]
  | otherwise = case as of
      [] -> []
      a : as' -> ((a :) <$> chooseFrom' (n - 1) (m - 1) as') ++ chooseFrom' n (m - 1) as'

deleteItems :: Ord k => Bag k -> Set.Set k -> Bag k
deleteItems bag ks = bag Bag.\\ Bag.fromSet ks

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