{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.DFA(
  DFA(),
  build,
  matches,
  produceStrings,
  debugPrint,
  fromNFA,
  toNFA,

  minimize,
  minimize_Brzozowski,
) where

import Data.Either (partitionEithers)
import Data.Foldable (for_)
import Data.List (sortOn)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as MV

import Data.Relation qualified as Rel
import Data.Relation.Labelled qualified as Rel.L

import Lang.NFA (NFA(..))
import Lang.NFA qualified as NFA

data DFA c = DFA
  { transition :: V.Vector (Map c Int),
    accepts :: V.Vector Bool
  }
  deriving (Show, Eq)

matches :: forall c. (Ord c) => [c] -> DFA c -> Bool
matches xs (DFA tr acc) = go 0 xs
  where
    go i [] = acc V.! i
    go i (c : rest) = case Map.lookup c (tr V.! i) of
      Nothing -> False
      Just j -> go j rest

produceStrings :: forall c. DFA c -> [[c]]
produceStrings (DFA tr acc) = concat $ table V.! 0
  where
    table :: V.Vector [[[c]]]
    table = V.zipWith make tr acc

    make :: Map c Int -> Bool -> [[[c]]]
    make nexts isAcc = [[] | isAcc] : foldr plus [] nexts'
      where
        plus :: forall x. [[x]] -> [[x]] -> [[x]]
        plus [] ys = ys
        plus xs [] = xs
        plus (x : xs) (y : ys) = (x ++ y) : plus xs ys

        nexts' = [map (map (c :)) (table V.! j) | (c, j) <- Map.toList nexts]

debugPrint :: (Show c) => DFA c -> IO ()
debugPrint (DFA tr acc) = do
  putStrLn "[DFA]"
  putStrLn $ "size: " ++ show (V.length tr)
  putStrLn $ "edges:"
  for_ (V.toList (V.indexed tr)) $ \(i, next) ->
    for_ (Map.toList next) $ \(c, j) ->
      putStrLn $ "  " ++ show i ++ " -(" ++ show c ++ ")-> " ++ show j
  putStrLn $ "accepts: " ++ show (V.toList acc)

toNFA :: DFA c -> NFA c
toNFA (DFA tr acc) = NFA (V.length tr) Map.empty edges acceptSet
  where
    edges =
      Map.fromList
        [(i, Map.map Set.singleton es) | (i, es) <- V.toList (V.indexed tr)]
    acceptSet = Set.fromList $ V.ifoldr (\i b r -> if b then i : r else r) [] acc

build :: (Ord s, Ord c) => s -> (s -> Map c s) -> (s -> Bool) -> DFA c
build initialState transitionFn isAccepting = DFA transitionTable acceptsTable
  where
    substMap = go Map.empty [initialState]
    go subst [] = subst
    go subst (s : rest)
      | s `Map.member` subst = go subst rest
      | otherwise =
          let next = transitionFn s
              subst' = Map.insert s (Map.size subst, next) subst
           in go subst' (Map.elems next ++ rest)
    table = V.create $ do
      v <- MV.new (Map.size substMap)
      for_ (Map.toList substMap) $ \(s, (i, next)) -> do
        let next' = Map.map (\s' -> fst (substMap Map.! s')) next
        MV.write v i (next', isAccepting s)
      pure v
    (transitionTable, acceptsTable) = V.unzip table

-- DFA conversion by powerset construction
fromNFA :: forall c. (Ord c) => NFA c -> DFA c
fromNFA net = build initialState transitionFn isAccepting
  where
    NFA _ epsEdges edges acc = NFA.propagateEpsilon $ NFA.trim net
    reach i = Set.insert i (Rel.lookup i epsEdges)

    initialState :: Set Int
    initialState = reach 0

    transitionFn :: Set Int -> Map c (Set Int)
    transitionFn as = nexts
      where
        as' = Set.unions $ map reach (Set.toList as)
        nexts = foldl' Rel.union Map.empty $ map (\a -> Map.findWithDefault Map.empty a edges) (Set.toList as')

    isAccepting :: Set Int -> Bool
    isAccepting as = not (Set.disjoint as acc)

emptyDFA :: DFA c
emptyDFA = DFA (V.fromList [Map.empty]) (V.fromList [False])

reverseDFA :: (Ord c) => DFA c -> DFA c
reverseDFA = fromNFA . NFA.reverse . toNFA

minimize_Brzozowski :: (Ord c) => DFA c -> DFA c
minimize_Brzozowski = reverseDFA . reverseDFA

vectorToMap :: V.Vector a -> Map Int a
vectorToMap = Map.fromDistinctAscList . V.toList . V.indexed

-- Hopcroft
minimize :: forall c. (Ord c) => DFA c -> DFA c
minimize dfa@(DFA transitionTab acceptsTab) = remap finalPartition dfa
  where
    alphabets :: Set c
    alphabets = foldMap Map.keysSet transitionTab

    -- Temporary "reject" state
    reject :: Int
    reject = -1

    allStates = Set.fromDistinctAscList [0 .. V.length transitionTab - 1]
    acceptSet = Set.filter (acceptsTab V.!) allStates
    rejectSet = Set.insert reject $ allStates Set.\\ acceptSet

    initialPartition = MkPartition $ Set.fromList [PC acceptSet, PC rejectSet]

    hopcroft :: Partition Int -> Partition Int -> [Set Int] -> Partition Int
    hopcroft parts working [] = case minViewP working of
      Nothing -> parts
      Just (as, working') -> hopcroft parts working' (Map.elems (intoSets as))
    hopcroft parts working (xs : rest) = hopcroft parts' working' rest
      where
        (parts', splits) = splitsBy xs parts
        (MkPartition workingSets, _) = splitsBy xs working
        pickSmaller (as, bs) = if sizePC as <= sizePC bs then as else bs
        working' = MkPartition $ Set.union workingSets (Set.fromList (pickSmaller <$> splits))

    intoSets :: Set Int -> Map c (Set Int)
    intoSets = foldl' (\acc a -> Rel.union acc (Map.findWithDefault Map.empty a revTransitionRel)) Map.empty
      where
        def = Map.fromSet (const reject) alphabets
        defaultToReject next = Map.union next def

        transitionRel =
          vectorToMap $
            V.map (Map.map Set.singleton . defaultToReject) $
              transitionTab

        revTransitionRel = Rel.L.transpose transitionRel

    resultPartition = hopcroft initialPartition initialPartition []
    finalPartition = filterP (Set.notMember reject) resultPartition

remap :: Partition Int -> DFA c -> DFA c
remap (MkPartition p) (DFA transitionTab acceptsTab)
  | null p = emptyDFA
  | otherwise = DFA newTransition newAccepts
  where
    bss = V.fromList $ sortOn reprPC $ Set.toList p
    subst = Map.unions [Map.fromSet (const i) (unPC bs) | (i, bs) <- V.toList (V.indexed bss)]
    substNext = Map.mapMaybe (`Map.lookup` subst)
    newTransition = V.map (substNext . (transitionTab V.!) . reprPC) bss
    newAccepts = V.map (\pc -> acceptsTab V.! reprPC pc) bss

-----------------------------------------

newtype Partition a = MkPartition (Set (PC a))
  deriving (Eq, Ord)

minViewP :: Partition a -> Maybe (Set a, Partition a)
minViewP (MkPartition ass) = case Set.minView ass of
  Just (PC as, rest) -> Just (as, MkPartition rest)
  Nothing -> Nothing

filterP :: (Ord a) => (Set a -> Bool) -> Partition a -> Partition a
filterP cond (MkPartition ass) = MkPartition $ Set.filter (cond . unPC) ass

splitsBy :: (Ord a) => Set a -> Partition a -> (Partition a, [(PC a, PC a)])
splitsBy as (MkPartition bss) = (MkPartition bss', splitPC)
  where
    part (PC bs)
      | Set.null bs0 || Set.null bs1 = Left (PC bs)
      | otherwise = Right (PC bs0, PC bs1)
      where
        bs0 = bs `Set.intersection` as
        bs1 = bs Set.\\ as

    (keptPC, splitPC) = partitionEithers $ part <$> Set.toList bss
    bss' = Set.fromList $ keptPC ++ (splitPC >>= \(bs0, bs1) -> [bs0, bs1])

-- | Component of a partition
newtype PC a = PC {unPC :: Set a}

sizePC :: PC a -> Int
sizePC = Set.size . unPC

-- | Representative element
reprPC :: PC a -> a
reprPC = Set.findMin . unPC

instance (Ord a) => Semigroup (PC a) where
  PC as <> PC bs = PC (Set.union as bs)

instance (Eq a) => Eq (PC a) where
  as == bs = sizePC as == sizePC bs && reprPC as == reprPC bs

instance (Ord a) => Ord (PC a) where
  compare = comparing (\as -> (sizePC as, reprPC as))
