{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
module Math.Graph.Quiver(
  -- Basics
  EdgeId, VertexId,
  Quiver(..),

  -- Building
  empty, overlay,
  fromEdgeList,
  fromEdgeList',
  fromEdgeList'',

  -- cycle decomposition
  isBalanced,
  Cycle(..),
  simplify,

  -- utilities
  EdgeSubst, emptySubst, applySubst, compSubst,

  -- debug
  test1, test2, test3,
  prettyQuiver
) where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Control.Monad (guard)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Foldable (fold)

type EdgeId = Int
type VertexId = Int

newtype Quiver = Quiver {
    -- | (Source vert id => Target vert id => Edge id)
    vertices :: IntMap (IntMap IntSet)
  }
  deriving (Eq, Ord)

prettyQuiver :: Quiver -> [String]
prettyQuiver (Quiver vs) = ["Quiver{"] ++ pprEdges ++ ["}"]
  where
    pprEdges = do
      (s, adj_s) <- IntMap.toAscList vs
      (t, stEdges) <- IntMap.toAscList adj_s
      e <- IntSet.toAscList stEdges
      pure $ " " ++ show s ++ "-[" ++ show e ++ "]->" ++ show t ++ ";"

instance Show Quiver where
  -- Maybe not ideal thing to do, but easier
  show = unlines . prettyQuiver

-- | Empty quiver.
empty :: Quiver
empty = Quiver { vertices = IntMap.empty }

-- | Combine two quivers on the same set of vertices,
--   while taking disjoint union for their edge IDs.
--
--   @overlay g1 g2@ returns "renaming map" @rename :: IntMap (Either EdgeId EdgeId)@
--   and the resulted quiver @g' :: Quiver@ paired.
--
--   The @rename@ map represents which edges in the result @g'@ corresponds to
--   which edge of which operands @g1, g2@.
--
--   An entry of @(e', e_orig)@ in @rename@ means that the edge represented by
--   id @e' :: EdgeId@ in the result @g'@ corresponds to
--
--   - @e1@ from the first operand @g1@ if @e_orig = Left e1@
--   - @e2@ from the second operand @g2@ if @e_orig = Right e2@ 
overlay :: Quiver -> Quiver -> (IntMap (Either EdgeId EdgeId), Quiver)
overlay (Quiver g1) (Quiver g2) = (rename, Quiver g')
  where
    edges1 = foldMap fold g1
    edges2 = foldMap fold g2
    
    maxEdgeId1 = maybe 0 fst $ IntSet.maxView edges1
    minEdgeId2 = maybe (maxEdgeId1 + 1) fst $ IntSet.minView edges2
    -- By shifting all IDs in g2 so that all IDs in g2 is at least (maxEdgeId1 + 1),
    -- ensure disjointness of edge IDs in the result.
    offset = maxEdgeId1 - minEdgeId2 + 1
    g2' = IntMap.map (IntMap.map (IntSet.mapMonotonic (offset +))) g2

    -- (e1, Left e1) entries 
    rename1 = IntMap.fromSet Left edges1
    -- (e2 + offset, Right e2) entries
    rename2 = IntMap.fromSet (Right . subtract offset) $ IntSet.mapMonotonic (offset +) edges2
    
    -- Combine to make the result
    rename = IntMap.union rename1 rename2
    g' = IntMap.unionWith (IntMap.unionWith IntSet.union) g1 g2'

fromEdgeList :: (Ord e, Ord v) => [(v, e, v)] -> (Quiver, Map v VertexId, IntMap e)
fromEdgeList edgeList = (graph, vertexSubst, edgeLabel)
  where
    edgeLabel = IntMap.fromDistinctAscList $ zipWith (\i (_,e,_) -> (i,e)) [0..] edgeList
    edgeList' = map (\(s,_,t) -> (s,t)) edgeList
    (graph, vertexSubst) = fromEdgeList' edgeList'

fromEdgeList' :: (Ord v) => [(v, v)] -> (Quiver, Map v VertexId)
fromEdgeList' edgeList = (fromEdgeList'' edgeList', vertexSubst)
  where
    lup subst v = case Map.lookup v subst of
      Nothing -> (Map.size subst, Map.insert v (Map.size subst) subst)
      Just k  -> (k, subst)
    
    loop subst [] = ([], subst)
    loop subst ((s,t) : rest) =
      let (i, subst') = lup subst s
          (j, subst'') = lup subst' t
      in case loop subst'' rest of
           ~(result, substResult) -> ((i,j) : result, substResult)
    
    (edgeList', vertexSubst) = loop Map.empty edgeList

fromEdgeList'' :: [(VertexId, VertexId)] -> Quiver
fromEdgeList'' edgeList = Quiver vs
  where
    edgeListWithId = zip [0..] edgeList
    vs = IntMap.fromListWith (IntMap.unionWith IntSet.union) $
      singleEdge <$> edgeListWithId
    singleEdge (e,(i,j)) = (i, IntMap.singleton j (IntSet.singleton e))

-- | outdegree == indegree on each vertex
isBalanced :: Quiver -> Bool
isBalanced Quiver{ vertices = g } = all (== 0) balance
  where
    balance = IntMap.fromListWith (+) $ do
      (s, adj_s) <- IntMap.toList g
      (t, es) <- IntMap.toList adj_s
      let weight = IntSet.size es
      [(s, -weight), (t, weight)]

lookupEdgeSet :: VertexId -> VertexId -> Quiver -> IntSet
lookupEdgeSet s t Quiver{ vertices = vs } =
  case IntMap.lookup s vs of
    Nothing -> IntSet.empty
    Just neighbor -> IntMap.findWithDefault IntSet.empty t neighbor

nonEmptySet :: IntSet -> Maybe IntSet
nonEmptySet x
  | IntSet.null x = Nothing
  | otherwise = Just x

dual :: Quiver -> Quiver
dual g = Quiver vs'
  where
    vs' = IntMap.fromListWith IntMap.union
      [ (t, IntMap.singleton s stEdges)
        | (s, te) <- IntMap.toList (vertices g)
        , (t, stEdges) <- IntMap.toList te ]

deleteEdge :: VertexId -> VertexId -> EdgeId -> Quiver -> Quiver
deleteEdge s t e Quiver{ vertices = vs } =
  let del = IntMap.update (nonEmptySet . IntSet.delete e) t
      vs' = IntMap.adjust del s vs
  in Quiver vs'

deleteEdges :: [(VertexId, VertexId, EdgeId)] -> Quiver -> Quiver
deleteEdges targets g = foldl' (\g' (s,t,e) -> deleteEdge s t e g') g targets

-- * Cycle decomposition

newtype Cycle = Cycle [EdgeId]
  deriving (Show, Eq, Ord)

cycleEdges :: Cycle -> [EdgeId]
cycleEdges (Cycle es) = es

--- | Separate self loops (1-cycles) from a quiver.
eliminateSelfLoops :: Quiver -> ([Cycle], Quiver)
eliminateSelfLoops g = (toCycle <$> selfLoops, deleteEdges selfLoops g)
  where
    toCycle (_,_,e) = Cycle [e]
    selfLoops =
      [(s,s,e) | (s, te) <- IntMap.toList (vertices g)
               , e <- maybe [] IntSet.toList $ IntMap.lookup s te ]

--- | Separate 2-cycles (pairs of edges of oppsite directions between two vertices)
---   from a quiver.
---
---   Generally, there can be multiple edge for both @s -> t@ and @t -> s@ directions.
---   This function makes as many as possible disjoint pairs out of
---   multiple @s -> t@ edges and @t -> s@ edges,
---   making arbitrary choice of how to pair them.
---   
---   For example, if there are three @s -> t@ edges and nine @t -> s@ edges,
---   this function makes three 2-cycles on @s -> t -> s@, leaving six @t -> s@
---   edges in the "residue" quiver.
eliminate2Cycles :: Quiver -> ([Cycle], Quiver)
eliminate2Cycles g = (toCycle <$> pairs, deleteEdges usedEdges g)
  where
    pairs = do
      (s,te) <- IntMap.toList (vertices g)
      (t,stEdges) <- IntMap.toList te
      guard (t > s)
      let tsEdges = lookupEdgeSet t s g
      zipWith (s,t,,) (IntSet.toList stEdges) (IntSet.toList tsEdges)
    
    toCycle (_,_, e1, e2) = Cycle [e1, e2]
    usedEdges = pairs >>= \(s,t,e1,e2) -> [(s,t,e1),(t,s,e2)]

--- | Separate 1- or 2- cycles from a quiver.
eliminateShortCycles :: Quiver -> ([Cycle], Quiver)
eliminateShortCycles g =
  let (cs1, g') = eliminateSelfLoops g
      (cs2, g'') = eliminate2Cycles g'
  in (cs1 ++ cs2, g'')

-- | "Contract" every vertex @v@ such that its all incoming edges are from @u@,
--   all outgoing edges are to @w@, and the number of edges match.
--   (For a quiver which 'isBalanced', the "matching number" condition is
--   automatic.)
--
--   Concretely, delete such @v@ and all @v -> w@ edges,
--   while reconnecting all @u -> v@ edges to @w@, and
--   returning edge substitution for record.
--   
--   When there are multiple edges between @u -> v@ and @v -> w@,
--   they are paired in an arbitrary manner.
--   (currently just zips the two lists of edge Ids)
contractVertices :: Quiver -> (EdgeSubst, Quiver)
contractVertices g = (edgeSubstAlive, Quiver vs'')
  where
    dualG = dual g
    targets = do
      (v, we) <- IntMap.toList (vertices g)
      -- Restrict to single-out single-in case
      -- Failing pattern match in [] monad is mzero
      [(w,vwEdges)] <- pure $ IntMap.toList we
      Just [(u,uvEdges)] <- pure $ IntMap.toList <$> IntMap.lookup v (vertices dualG)
      guard (IntSet.size vwEdges == IntSet.size uvEdges)
      pure (u,uvEdges,v,vwEdges,w)
    
    deletedVertices = IntSet.fromList [ v | (_, _, v, _, _) <- targets ]
    app subst v = IntMap.findWithDefault v v subst
    vertexSubst = fst $ foldl' step (IntMap.empty, IntMap.empty) vertexRenames
      where
        vertexRenames = [ (v,w) | (_,_,v,_,w) <- targets ]
        step (!subst, !substInv) (v,w) =
          let w' = app subst w
              v' = app substInv v
              subst' = IntMap.insert v' w' $ IntMap.delete v subst
              substInv' = IntMap.insert w' v' $ IntMap.delete w substInv
          in (subst', substInv')
    deletedEdges = IntSet.unions [ vwEdges | (_, _, _, vwEdges, _) <- targets ]

    contractLog = do
      (_,uvEdges,_,vwEdges,_) <- targets
      zip (IntSet.toList uvEdges) (IntSet.toList vwEdges)
    edgeSubstAll = foldl' (\s (uv, vw) -> compSubst (singleSubst uv [uv,vw]) s) emptySubst contractLog

    edgeSubstAlive = IntMap.withoutKeys edgeSubstAll deletedEdges
    vs' = IntMap.withoutKeys (vertices g) deletedVertices
    vs'' = foldl' step vs' edgeReconnects
      where
        edgeReconnects = 
          [ (u, uvEdges, v)
            | (u, uvEdges, v, _, _) <- targets,
              u `IntSet.notMember` deletedVertices ]
        step vs1 (u, uvEdges, v) = IntMap.adjust recon u vs1
          where
            w' = app vertexSubst v
            recon =
              IntMap.insertWith IntSet.union w' uvEdges . IntMap.delete v

type EdgeSubst = IntMap [EdgeId]

emptySubst :: EdgeSubst
emptySubst = IntMap.empty

singleSubst :: EdgeId -> [EdgeId] -> EdgeSubst
singleSubst = IntMap.singleton

applySubst :: EdgeSubst -> EdgeId -> [EdgeId]
applySubst subst e = IntMap.findWithDefault [e] e subst

-- | @applySubst (compSubst s1 s2) === applySubst s1 >=> applySubst s2@
--   
--   Beware of the order of composition: it's not the order of @(.)@ or @(<=<)@,
--   but diagrammatic order @(>>>), (>=>)@ 
compSubst :: EdgeSubst -> EdgeSubst -> EdgeSubst
compSubst s1 s2 = IntMap.union (IntMap.map (>>= applySubst s2) s1) s2

substCycle :: EdgeSubst -> Cycle -> Cycle
substCycle subst (Cycle es) = Cycle $ es >>= applySubst subst

simplify :: Quiver -> ([Cycle], EdgeSubst, Quiver)
simplify = simpLoop emptySubst
  where
    simpLoop subst g = case eliminateShortCycles g of
      (csPreSubst, g') ->
        let cs = map (substCycle subst) csPreSubst
            subst' = IntMap.withoutKeys subst (IntSet.fromList (csPreSubst >>= cycleEdges))
            (newSubst, g'') = contractVertices g'
            subst'' = compSubst newSubst subst'
        in if null cs && IntMap.null newSubst
             then ([], subst', g'')
             else case simpLoop subst'' g'' of
                    ~(csRest, finalSubst, g''') -> (cs ++ csRest, finalSubst, g''')

----

test1, test2 :: Quiver
test1 = fromEdgeList'' [
    (1,2), (1,4),
    (2,3), (2,3),
    (3,1), (3,5),
    (4,1), (4,2),
    (5,4)
  ]
test2 = fromEdgeList'' [
  (1,2), (1,4),
  (2,3), (2,3),
  (3,1), (3,4), (3,4),
  (4,2), (4,5), (4,5),
  (5,1), (5,3)
  ]

-- >>> isBalanced test1
-- True

-- >>> (cs1, test1') = eliminate2Cycles test1
-- >>> cs1
-- >>> test1
-- >>> test1'
-- [Cycle [1,6]]
-- Quiver{
--  1-[0]->2;
--  1-[1]->4;
--  2-[2]->3;
--  2-[3]->3;
--  3-[4]->1;
--  3-[5]->5;
--  4-[6]->1;
--  4-[7]->2;
--  5-[8]->4;
-- }
-- Quiver{
--  1-[0]->2;
--  2-[2]->3;
--  2-[3]->3;
--  3-[4]->1;
--  3-[5]->5;
--  4-[7]->2;
--  5-[8]->4;
-- }
-- >>> (subst, test1'') = contractVertices test1'
-- >>> subst
-- >>> test1''
-- fromList [(4,[4,0]),(5,[5,8,7])]
-- Quiver{
--  2-[2]->3;
--  2-[3]->3;
--  3-[4]->2;
--  3-[5]->2;
-- }

-- >>> simplify test1
-- ([Cycle [1,6],Cycle [2,4,0],Cycle [3,5,8,7]],fromList [],Quiver{
-- }
-- )
-- >>> simplify test2
-- ([],fromList [],Quiver{
--  1-[0]->2;
--  1-[1]->4;
--  2-[2]->3;
--  2-[3]->3;
--  3-[4]->1;
--  3-[5]->4;
--  3-[6]->4;
--  4-[7]->2;
--  4-[8]->5;
--  4-[9]->5;
--  5-[10]->1;
--  5-[11]->3;
-- }
-- )

test3 :: Quiver
test3 = snd $ overlay test1 test2

-- >>> test3
-- Quiver{
--  1-[0]->2;
--  1-[9]->2;
--  1-[1]->4;
--  1-[10]->4;
--  2-[2]->3;
--  2-[3]->3;
--  2-[11]->3;
--  2-[12]->3;
--  3-[4]->1;
--  3-[13]->1;
--  3-[14]->4;
--  3-[15]->4;
--  3-[5]->5;
--  4-[6]->1;
--  4-[7]->2;
--  4-[16]->2;
--  4-[17]->5;
--  4-[18]->5;
--  5-[19]->1;
--  5-[20]->3;
--  5-[8]->4;
-- }
-- >>> simplify test3
-- ([Cycle [1,6],Cycle [5,20],Cycle [17,8],Cycle [10,18,19],Cycle [2,4,0],Cycle [3,13,9],Cycle [11,14,7],Cycle [12,15,16]],fromList [],Quiver{
-- }
-- )
