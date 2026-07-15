{-# LANGUAGE BangPatterns #-}
module DistanceProfile(

  -- * Search logic
  searchAll, searchAllModuloPermutation,

  {-
  -- ** Types in use
  Interval(..),
  SymMat(..), newMat, at, set,
  -}

  -- ** Type of the resulted distance matrix
  DM(),
  prettyTable,

  -- * Example inputs
  squareProf, rectProf, cubeProf, cube4Prof,
) where

import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntMultiSet as IMS

import Control.Monad.State
import Control.Monad (MonadPlus(..), forM, guard)
import Control.Monad.Reader
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Data.List (sort)
import qualified Data.Vector.Unboxed as UV
import Control.Exception (assert)

import Text.Table
import Data.Set (Set)
import EquivalenceUtil (uniqueUpTo)

-- * Distance matrix
data DM = MkDM Int (UV.Vector Int)
  deriving (Eq, Ord, Show)

makeDM :: Int -> (Int -> Int -> Int) -> DM
makeDM n f = MkDM n $ UV.fromListN (triangular (n - 1)) dmContent
  where
    dmContent = do
      j <- [0 .. n - 1]
      i <- [0 .. j - 1]
      pure $ f i j

indexDM :: DM -> Int -> Int -> Int
indexDM (MkDM n vec) = f
  where
    f i j
      | i == j = 0
      | 0 <= i && i < n && 0 <= j && j < n = vec UV.! (min i j + triangular (max i j - 1))
      | otherwise = error $ "out of bounds: " ++ show (n,i,j)

-- | Convert to table for pretty-printing
prettyTable :: DM -> Table
prettyTable dm@(MkDM n _) = Table n n (\i j -> show (indexDM dm i j))

transposition :: Int -> Int -> Int -> Int
transposition s t k
  | k == s = t
  | k == t = s
  | otherwise = k

permuteDM :: Int -> (Int -> Int) -> DM -> DM
permuteDM n f = apply
  where
    perm = UV.fromListN (triangular (n - 1)) permList
    permList = do
      j <- [0 .. n - 1]
      i <- [0 .. j - 1]
      let i' = f i
          j' = f j
      pure $ min i' j' + triangular (max i' j' - 1)
    
    apply (MkDM n' vec)
      | n /= n' = error $ "applying to DM of wrong size: " ++ show (n,n')
      | otherwise = MkDM n $ UV.backpermute vec perm

regularize :: DM -> DM
regularize dm@(MkDM n _) = permuteDM n (sortingPerm UV.!) dm
  where
    firstRow = [ (indexDM dm 0 j, j) | j <- [0 .. n - 1] ]
    sortingPerm = UV.fromListN n (snd <$> sort firstRow)

moduloPermutation :: [Int] -> [DM] -> [DM]
moduloPermutation profList = uniqueUpTo (shellPermGenerators n p ++ basepointChanges)
  where
    n = 1 + length profList
    p = profileFromList profList
    basepointChanges = do
      j <- [1 .. n - 1]
      pure $ regularize . permuteDM n (transposition 0 j)

shellPermGenerators :: Int -> Profile -> [DM -> DM]
shellPermGenerators n p =
  let dists = IMS.toAscList p
      sameDistSwaps =
        [ (i,i+1) | (i,di,dj) <- zip3 [1..] dists (drop 1 dists), di == dj]
  in permuteDM n . uncurry transposition <$> sameDistSwaps

-- * Types to write search algorithms

-- ** Intervals

data Interval = I !Int !Int
  deriving (Eq, Ord, Show)

isSingleton :: Interval -> Bool
isSingleton (I lo hi) = lo == hi

intersectInterval :: Interval -> Interval -> Maybe Interval
intersectInterval (I xLo xHi) (I yLo yHi)
  | lo > hi = Nothing
  | otherwise = Just (I lo hi)
  where
    lo = max xLo yLo
    hi = min xHi yHi

-- | Narrows down 3 ranges of edge lengths using triangle inequality
narrow :: (Interval, Interval, Interval) -> Maybe (Interval, Interval, Interval)
narrow (xs, ys, zs) =
  (,,) <$> narrowOne (xs, ys, zs)
       <*> narrowOne (ys, zs, xs)
       <*> narrowOne (zs, xs, ys)

-- | Narrow x range using triangle inequality
narrowOne :: (Interval, Interval, Interval) -> Maybe Interval
narrowOne (xs, I yLo yHi, I zLo zHi)
  -- Precondition: (0 <= xLo <= xHi), (0 <= yLo <= yHi), (0 <= zLo <= zHi)
  = intersectInterval xs (I gap top)
  where
    -- Pair (y,z) moves inside [yLo .. yHi] × [zLo .. zHi].
    -- A valid value of x must be in the union of the interval
    -- coming from triangle inequality
    --
    -- |y - z| <= x <= y + z
    --
    -- for each choice of (y,z). therefore
    --
    -- gap = minimum [ abs (y - z) | y <- [yLo .. yHi], z <- [zLo .. zHi] ]
    -- top = maximum [ y + z | y <- [yLo .. yHi], z <- [zLo .. zHi] ]
    -- 
    -- and x ∈ [xLo .. xHi] ∩ [gap .. top].
    gap = max 0 (max (zLo - yHi) (yLo - zHi))
    top = yHi + zHi

-- ** Symmetric matrix
data SymMat a = SymMat { matElems :: !(IntMap a), matDefault :: !a }
  deriving (Eq, Ord, Show)

newMat :: a -> SymMat a
newMat = SymMat IntMap.empty

triangular :: Int -> Int
triangular n = ((n + 1) * n) `div` 2

at :: (Int,Int) -> SymMat a -> a
at (i,j) dm = IntMap.findWithDefault (matDefault dm) key (matElems dm)
  where
    key = min i j + triangular (max i j)

set :: Eq a => (Int,Int) -> a -> SymMat a -> SymMat a
set (i,j) val dm
  | val == matDefault dm = dm{ matElems = IntMap.delete key (matElems dm) }
  | otherwise = dm{ matElems = IntMap.insert key val (matElems dm) }
  where
    key = min i j + triangular (max i j)

-- ** Distance profile
type Profile = IMS.IntMultiSet

profileFromList :: [Int] -> Profile
profileFromList ds
  | all (> 0) ds = IMS.fromList ds
  | otherwise = error "invalid profile"

-- * Search Monad
type SearchM = ReaderT SearchCtx (StateT SearchState [])
type SearchCtx = Int -- the number of points
data SearchState = SearchState {
    -- | Set of edges not yet committed to a single value.
    uncomitted :: Set (Int, Int),
    -- | Possible distances, managed as intervals.
    --   For a commited edge, the interval is the singleton interval (I d d). 
    distRange :: SymMat Interval,
    -- | Multiset of distances from each vertex,
    --   not yet used by commited edges.
    remainProfile :: IntMap Profile
  }
  deriving Show

runSearchM :: Int -> Profile -> SearchM () -> [SymMat Interval]
runSearchM n profile body = distRange <$> execStateT (runReaderT body ctx) state0
  where
    initialRange = I (IMS.findMin profile) (IMS.findMax profile)
    allEdges = Set.fromList [ (i,j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1] ]
    
    ctx = n
    state0 = SearchState{
      uncomitted = allEdges,
      distRange = newMat initialRange,
      remainProfile = IntMap.fromDistinctAscList
        [ (i, profile) | i <- [0 .. n - 1]]
    }

getDistRange :: (Int,Int) -> SearchM Interval
getDistRange ij = gets (dGet ij . distRange)
  where
    -- same to @at (i,j)@ except it returns @I 0 0@ for diagonal
    dGet (i,j) dm
      | i == j = I 0 0
      | otherwise = at (i,j) dm

putDistRange :: (Int,Int) -> Interval -> SearchM ()
putDistRange ij val = do
  modify' $ \st ->
    let !dist' = set ij val (distRange st)
    in st{ distRange = dist'}

-- ** Main search logic

searchAll :: [Int] -> [DM]
searchAll profList
  -- Degenerate case: profile is empty; there's only one point
  | n == 1 = pure $ makeDM 1 (\_ _ -> 0)
  -- Degenerate case 2:
  --   profile is @n - 1@ equal distances; the result is unique
  | IMS.distinctSize p == 1 = 
      pure $ let d0 = IMS.findMin p in makeDM n (\_ _ -> d0)
  | otherwise = do
      let firstRow = [((0,j), I d d) | (j, d) <- zip [1..] (sort profList)]
      dist <- runSearchM n p $ do
        enterAll firstRow
        solveLoop
        validateFinalState
      let dm = makeDM n (\i j -> getLo $ at (i,j) dist)
      assert (checkProfile dm) pure dm
  where
    n = 1 + length profList
    p = profileFromList profList
    getLo (I lo _) = lo

    checkProfile dm = all (== p) $ do
      i <- [0 .. n - 1]
      let distanceList = [ indexDM dm i j | j <- [0 .. n - 1], i /= j]
      pure $ profileFromList distanceList

searchAllModuloPermutation :: [Int] -> [DM]
searchAllModuloPermutation profList = moduloPermutation profList (searchAll profList)

-- | Add constraints and propagate them until it converges
enterAll :: [((Int,Int),Interval)] -> SearchM ()
enterAll [] = pure ()
enterAll (def : defs) = do
  newDefs <- enter def
  enterAll (newDefs ++ defs)

-- | Add new constraint that the distance of edge (i,j) must be included in
--   an @xRange@, then propagate the change.
enter :: ((Int,Int),Interval) -> SearchM [((Int,Int),Interval)]
enter (ij, xRange) = do
  xRange0 <- getDistRange ij
  Just xRange' <- pure $ intersectInterval xRange xRange0
  if xRange' == xRange0
    then pure []
    else do
      putDistRange ij xRange'
      if isSingleton xRange' then do
        let I d _ = xRange'
        commit ij d
        propagate ij
      else pure []

-- | Distance of edge (i,j) is fixed to d and record (i,j) to be already committed.
--   Take d out from the multisets of "remaining" distances for both i and j.
--   Fail if d was not in both of the multisets.
commit :: (Int,Int) -> Int -> SearchM ()
commit (i,j) d = do
  -- Delete from uncomitted edges
  modify' $ \st -> st{
      uncomitted = Set.delete (min i j, max i j) (uncomitted st)
    }
  -- Update remaining distance profiles
  profs <- gets remainProfile
  let p = profs IntMap.! i
      q = profs IntMap.! j
  guard $ IMS.member d p
  guard $ IMS.member d q
  let p' = IMS.delete d p
      q' = IMS.delete d q
      profs' = IntMap.insert i p' (IntMap.insert j q' profs)
  modify' $ \st -> st{
      remainProfile = profs'
    }

-- | For an edge (i,j), check each triangle inequalities containing (i,j)
--   to narrow down ranges for all relevant edges.
propagate :: (Int,Int) -> SearchM [((Int,Int), Interval)]
propagate (i,j) = do
  n <- ask
  let thirdVertices = [ k | k <- [0 .. n - 1], i /= k, j /= k ]
  updateResults <- forM thirdVertices $ \k -> do
    {-
       i
    x / \ y
     j---k
       z
    -}
    xRange <- getDistRange (i,j)
    yRange <- getDistRange (i,k)
    zRange <- getDistRange (j,k)
    Just (xRange', yRange', zRange') <- pure $ narrow (xRange, yRange, zRange)
    pure [ ((i,j),xRange'), ((i,k),yRange'), ((j,k),zRange') ]
  pure (concat updateResults)

-- | Guesses the distance of the edge.
--   (This function is the only branching in the search algorithm)
guess :: (Int,Int) -> SearchM Int
guess (i,j) = do
  profs <- gets remainProfile
  let p = profs IntMap.! i
      q = profs IntMap.! j
      candidates = IntSet.intersection (IMS.toSet p) (IMS.toSet q)
  choose $ IntSet.toList candidates 

solveLoop :: SearchM ()
solveLoop = do
  edges <- gets uncomitted
  case Set.lookupMin edges of
    Just ij -> do
      d <- guess ij
      enterAll [(ij, I d d)]
      solveLoop
    Nothing -> pure ()

validateFinalState :: SearchM ()
validateFinalState = ask >>= \n -> get >>= \st -> checks n st (pure ())
  where
    checks n st =
      assert (allRemainingProfilesAreEmpty (remainProfile st)) .
      assert (allRangesAreSingleton n (distRange st))
    allRemainingProfilesAreEmpty = all IMS.null
    allRangesAreSingleton n dist =
      all (\ij -> isSingleton (at ij dist)) allEdges
      where
        allEdges = [(i,j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1]]

-- * example profiles
squareProf, rectProf, cubeProf, cube4Prof :: [Int]
squareProf = [1,1,2]
rectProf = [1,2,3]
cubeProf = replicate 3 1 ++ replicate 3 2 ++ [3]
cube4Prof = replicate 4 1 ++ replicate 6 2 ++ replicate 4 3 ++ [4]

-- * Utility

choose :: (Foldable t, MonadPlus m) => t a -> m a
choose = foldr (\a r -> pure a `mplus` r) mzero

