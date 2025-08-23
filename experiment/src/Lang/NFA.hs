{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module Lang.NFA(
  NFA(..),
  debugPrint,

  -- * Basic construction
  fromExpr,
  empty, epsilon, lit,
  unions, union,
  concat, append,
  star,

  -- * Extra things
  reverse,
  trim,
  propagateEpsilon

) where

import Prelude hiding (concat, reverse)
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Map qualified as Map
import Data.Map (Map)
import Data.Foldable (for_)

import Data.Relation (Rel)
import Data.Relation qualified as Rel
import Data.Relation.Labelled qualified as Rel.L

import Lang.RegularExpression ( Expr(..) )

data NFA c = NFA
  {
    nfaSize :: !Int,
    nfaEpsilonEdges :: Rel Int Int,
    nfaTransitions :: Map Int (Map c (Set Int)),
    nfaAccepts :: Set Int
  }
  deriving Show

debugPrint :: Show c => NFA c -> IO ()
debugPrint (NFA size epsEdges edges acc) = do
  putStrLn "[NFA]"
  putStrLn $ "size: " ++ show size
  putStrLn $ "edges:"
  for_ (Map.toList epsEdges) $ \(i,js) ->
    for_ js $ \j ->
      putStrLn $ "  " ++ show i ++ " -> " ++ show j
  for_ (Map.toList edges) $ \(i,next) ->
    for_ (Map.toList next) $ \(c,js) ->
      for_ js $ \j ->
        putStrLn $ "  " ++ show i ++ " -(" ++ show c ++ ")-> " ++ show j
  putStrLn $ "accepts: "  ++ show (Set.toList acc)

fromExpr :: Ord c => Expr c -> NFA c
fromExpr = go
  where
    go (Lit c) = lit c
    go (Union exprs) = unions (go <$> exprs)
    go (Concat exprs) = concat (go <$> exprs)
    go (Star expr) = star (go expr)

-- | > (0)
empty :: NFA c
empty = NFA 1 Map.empty Map.empty Set.empty

-- | > (0)!
epsilon :: NFA c
epsilon = NFA 1 Map.empty Map.empty (Set.singleton 0)

-- | > (0) -[c]-> (1)!
lit :: c -> NFA c
lit c = NFA 2 Map.empty (Map.singleton 0 (Map.singleton c (Set.singleton 1))) (Set.singleton 1)

shift :: Int -> NFA c -> (Rel Int Int, Map Int (Map c (Set Int)), Set Int)
shift i (NFA _ epsEdges edges acc) = (epsEdges', edges', acc')
  where
    shiftSet = Set.mapMonotonic (i +)
    shiftMap = Map.mapKeysMonotonic (i +)

    epsEdges' = Map.map shiftSet $ shiftMap $ epsEdges
    edges' = Map.map (Map.map shiftSet) $ shiftMap $ edges
    acc' = shiftSet acc

unions :: [NFA c] -> NFA c
unions [] = empty
unions (net : nets) = foldl' union net nets

union :: NFA c -> NFA c -> NFA c
union (NFA size0 epsEdges0 edges0 accepts0) net1 = net'
  where
    (epsEdges1, edges1, accepts1) = shift size0 net1
    -- Merge edge sets (vertices are disjoint!)
    epsEdges' = Map.union epsEdges0 epsEdges1
    edges' = Map.union edges0 edges1
    -- Add epsilon edge from initial to initial of subnet
    epsEdges'' = Map.insertWith Set.union 0 (Set.singleton size0) epsEdges'
    -- Merge accepting state sets
    accepts' = Set.union accepts0 accepts1
    -- Combine everything together
    net' = NFA (size0 + nfaSize net1) epsEdges'' edges' accepts'

concat :: [NFA c] -> NFA c
concat [] = epsilon
concat (net : rest) = foldl' append net rest

append :: NFA c -> NFA c -> NFA c
append (NFA size0 epsEdges0 edges0 accepts0) net1 = net'
  where
    size' = size0 + nfaSize net1
    (epsEdges1, edges1, accepts1) = shift size0 net1
    epsEdges' = Map.union epsEdges0 epsEdges1
    edges' = Map.union edges0 edges1

    -- Epsilon edges connecting accepting state of net0 to initial state of net1
    connect01 = Map.fromSet (const (Set.singleton size0)) accepts0
    epsEdges'' = Rel.union epsEdges' connect01

    net' = NFA size' epsEdges'' edges' accepts1


star :: NFA c -> NFA c
star (NFA size epsEdges edges acc) = NFA size epsEdges' edges accepts'
  where
    epsEdges' = Rel.union epsEdges (Map.fromSet (const (Set.singleton 0)) acc)
    accepts' = Set.singleton 0

reverse :: Ord c => NFA c -> NFA c
reverse net = NFA size' epsEdges' edges' accepts'
  where
    -- Shift the net by one to create a fresh initial state
    size' = nfaSize net + 1
    (epsEdges0, edges0, accepts0) = shift 1 net

    -- the new accepting state is /the old initial state/
    accepts' = Set.singleton 1

    -- Reverse all epsilon edges + (new inital -> old accepting)
    newEpsEdges = Map.singleton 0 accepts0
    epsEdges' = Rel.union newEpsEdges (Rel.transpose epsEdges0)

    -- Reverse all edges
    edges' = Rel.L.transpose edges0

-- Cleanup NFA

-- - Remove nodes unreachable from start or to accepting

trim :: NFA c -> NFA c
trim (NFA size epsEdges edges acc) = NFA size epsEdges' edges' acc'
  where
    rel = Rel.transitiveClosure (Rel.union epsEdges (Rel.L.unlabel edges))

    reachableFromStart = Set.insert 0 $ Rel.lookup 0 rel
    reachableToAcc = Map.keysSet $ Map.filter (\bs -> not (Set.disjoint bs acc)) rel
    living = reachableFromStart `Set.intersection` (acc `Set.union` reachableToAcc)

    epsEdges' = Rel.restrict living living epsEdges
    edges' = Rel.L.restrict living living edges
    acc' = Set.intersection living acc

-- | Make epsilon edges transitive and propagate accepted-ness
--   via epsilon edges (backward)

propagateEpsilon :: NFA c -> NFA c
propagateEpsilon (NFA size epsEdges edges acc) = NFA size epsEdges' edges acc'
  where
    epsEdges' = Rel.transitiveClosure epsEdges
    hitsAcc bs = not (acc `Set.disjoint` bs)
    acc' = Set.union acc (Map.keysSet $ Map.filter hitsAcc epsEdges')
