{-# LANGUAGE BangPatterns #-}
module Math.Graph.Directed(
  VertexId,

  Digraph(..),
  fromEdgeList,
  allElemCircuits,

  filterVertex, deleteVertex,

  -- * for test
  regularTournament,
  acyclicTournament,
  allElemCircuitsNaive,
) where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type VertexId = Int

newtype Digraph = Digraph (IntMap IntSet)
  deriving (Show, Eq, Ord)

fromEdgeList :: [(VertexId, VertexId)] -> Digraph
fromEdgeList = Digraph . IntMap.fromListWith IntSet.union . map singleEdge
  where
    singleEdge (u,v) = (u, IntSet.singleton v)

data BlockState = BS !IntSet !(IntMap IntSet)

blockState0 :: BlockState
blockState0 = BS IntSet.empty IntMap.empty

isBlocked :: BlockState -> VertexId -> Bool
isBlocked (BS blocked _) v = IntSet.member v blocked

block :: BlockState -> VertexId -> BlockState
block (BS blocked reach) v = BS (IntSet.insert v blocked) reach

rememberParent :: BlockState -> VertexId -> IntSet -> BlockState
rememberParent (BS blocked reach) v ws = BS blocked reach'
  where
    -- reach' = {(w,v) | w \in ws} `union` reach
    reach' = IntMap.unionWith IntSet.union reach w2v
      where 
        w2v = IntMap.fromSet (const (IntSet.singleton v)) ws

unblock :: BlockState -> VertexId -> BlockState
unblock (BS blocked reach) v = case IntMap.lookup v reach of
  Nothing -> BS blocked' reach
  Just ws -> foldl' unblock (BS blocked' reach') (IntSet.toList (IntSet.intersection blocked' ws))
  where
    blocked' = IntSet.delete v blocked
    reach' = IntMap.delete v reach

-- | Johnson's elementary circuit enumeration algorithm
allElemCircuits :: Digraph -> [[VertexId]]
allElemCircuits graph@(Digraph edgeMap) = case IntMap.lookupMin edgeMap of
  Nothing -> []
  Just (root, _) -> circuits root ++ allElemCircuits (deleteVertex root graph)
  where
    circuits :: VertexId -> [[VertexId]]
    circuits root = case go root [] [] blockState0 of
        (outputs, _, _) -> reverse outputs
      where
        go :: VertexId -> [VertexId] -> [[VertexId]] -> BlockState -> ([[VertexId]], BlockState, Bool)
        go v path outputs b = (outputs'', b''', foundAny)
          where
            path' = v : path
            ws = IntMap.findWithDefault IntSet.empty v edgeMap
            b' = block b v
            foundCircuit = IntSet.member root ws
            outputs'
              | foundCircuit = reverse path' : outputs
              | otherwise    = outputs
            
            unblocked = IntSet.toList $ IntSet.filter (not . isBlocked b') ws
            (outputs'', b'', foundAny) = loop (v : path) outputs' b' foundCircuit unblocked
            b''' | foundAny  = unblock b'' v
                 | otherwise = rememberParent b'' v ws
        
        loop :: [VertexId] -> [[VertexId]] -> BlockState -> Bool -> [VertexId] -> ([[VertexId]], BlockState, Bool)
        loop path outputs b !foundAny ws = case ws of
          []    -> (outputs, b, foundAny)
          w:ws' -> case go w path outputs b of
            (outputs', b', foundAny') -> loop path outputs' b' (foundAny || foundAny') ws'

filterVertex :: (VertexId -> Bool) -> Digraph -> Digraph
filterVertex cond (Digraph g) = Digraph $ IntMap.mapMaybeWithKey del g
  where
    del x adj
      -- filter adjacency set
      | cond x = nonEmptySet (IntSet.filter cond adj)
      -- delete vertex x itself
      | otherwise = Nothing

deleteVertex :: VertexId -> Digraph -> Digraph
deleteVertex v (Digraph g) = Digraph $ IntMap.mapMaybeWithKey del g
  where
    del x adj
      -- delete vertex x itself
      | x == v = Nothing
      -- delete from adjacency set
      | otherwise = nonEmptySet (IntSet.delete v adj)

nonEmptySet :: IntSet -> Maybe IntSet
nonEmptySet x
  | IntSet.null x = Nothing
  | otherwise = Just x

----

-- | The acyclic tournament on @n@ vertices: i.e. @(i,j) ∈ E@ iff @i < j@.
acyclicTournament :: Int -> Digraph
acyclicTournament n = fromEdgeList $ do
  i <- [1 .. n]
  j <- [i + 1 .. n]
  pure (i,j)

-- | @2 * k + 1@ - vertices regular tournament (of specific, symmetric orientation)
regularTournament :: Int -> Digraph
regularTournament k = fromEdgeList $ do
  i <- [1 .. 2 * k + 1]
  j <- [1 .. k]
  pure (i, 1 + (i+j-1) `mod` (2 * k + 1))

-- >>> acyclicTournament 5
-- Digraph (fromList [(1,fromList [2,3,4,5]),(2,fromList [3,4,5]),(3,fromList [4,5]),(4,fromList [5])])
-- >>> allElemCircuits $ acyclicTournament 5
-- []
--
-- >>> regularTournament 1
-- Digraph (fromList [(1,fromList [2]),(2,fromList [3]),(3,fromList [1])])

-- >>> regularTournament 2
-- Digraph (fromList [(1,fromList [2,3]),(2,fromList [3,4]),(3,fromList [4,5]),(4,fromList [1,5]),(5,fromList [1,2])])

-- >>> allElemCircuits $ regularTournament 1
-- [[1,2,3]]
--
-- >>> allElemCircuits $ regularTournament 2
-- [[1,2,3,4],[1,2,3,4,5],[1,2,3,5],[1,2,4],[1,2,4,5],[1,3,4],[1,3,4,5],[1,3,5],[1,3,5,2,4],[2,3,4,5],[2,3,5],[2,4,5]]

-- >>> allElemCircuitsNaive $ regularTournament 1
-- [[1,2,3]]
--
-- >>> allElemCircuitsNaive $ regularTournament 2
-- [[1,2,3,4],[1,2,3,4,5],[1,2,3,5],[1,2,4],[1,2,4,5],[1,3,4],[1,3,4,5],[1,3,5],[1,3,5,2,4],[2,3,4,5],[2,3,5],[2,4,5]]

-- >>> length $ allElemCircuits (regularTournament 3)
-- 115

-- >>> map (length . allElemCircuits . regularTournament) [1 .. 6]
-- [1,12,115,1626,36085,1185736]
--
-- >>> map (length . allElemCircuitsNaive . regularTournament) [1 .. 6]
-- [1,12,115,1626,36085,1185736]

allElemCircuitsNaive :: Digraph -> [[VertexId]]
allElemCircuitsNaive graph@(Digraph edgeMap) = case IntMap.lookupMin edgeMap of
  Nothing -> []
  Just (root, _) -> circuits root ++ allElemCircuitsNaive (deleteVertex root graph)
  where
    circuits :: VertexId -> [[VertexId]]
    circuits root = go root IntSet.empty
      where
        go :: VertexId -> IntSet -> [[VertexId]]
        go v visited
          | IntSet.member v visited = []
          | otherwise               = [[v] | foundCircuit] ++ proceed
          where
            proceed = do
              w <- IntSet.toList ws
              rest <- go w visited'
              pure (v : rest)
            
            visited' = IntSet.insert v visited
            ws = IntMap.findWithDefault IntSet.empty v edgeMap
            foundCircuit = IntSet.member root ws
