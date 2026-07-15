{-# LANGUAGE BangPatterns #-}
module DistanceProfile(

  -- * Search logic
  searchAll,

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
import Data.Relation (Rel)
import qualified Data.Relation as Rel
import qualified Data.Vector as V

import Control.Monad.State
import Control.Monad (MonadPlus(..), forM, guard)
import Control.Monad.Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Data.List (sortOn, sort)
import Data.Ord (Down(..))
import qualified Data.Vector.Unboxed as UV
import Control.Exception (assert)

import Text.Table

-- * Intervals

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

-- Symmetric matrix
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

-- * Distance profile
type Profile = IMS.IntMultiSet

profileFromList :: [Int] -> Profile
profileFromList ds
  | all (> 0) ds = IMS.fromList ds
  | otherwise = error "invalid profile"

-- Search
type SearchM = ReaderT SearchCtx (StateT SearchState [])
type SearchCtx = V.Vector Triangle
data SearchState = SearchState {
    distRange :: SymMat Interval,
    remainProfile :: IntMap Profile,
    blockers :: Blocker
  }
  deriving Show

type Blocker = Rel (Int,Int) Int
type Triangle = (Int, Int, Int)

allTriangles :: Int -> V.Vector Triangle
allTriangles n = V.fromList $ do
  i <- [0 .. n - 1]
  j <- [i + 1 .. n - 1]
  k <- [j + 1 .. n - 1]
  pure (i,j,k)

searchAll :: [Int] -> [DM]
searchAll profList = do
  let n = 1 + length profList
      p = profileFromList profList
      firstRow = [((0,j), I d d) | (j, d) <- zip [1..] (sort profList)]
  dist <- runSearchM n p $ do
    enterAll firstRow
    solveLoop
  pure $ makeDM n dist

runSearchM :: Int -> Profile -> SearchM () -> [SymMat Interval]
runSearchM n p m = distRange <$> execStateT (runReaderT m ctx) state0
  where
    (ctx, state0) = initialState n p

initialState :: Int -> Profile -> (SearchCtx, SearchState)
initialState n profile = (trigs, state0)
  where
    trigs = allTriangles n
    initialRange = I (IMS.findMin profile) (IMS.findMax profile)
    state0 = SearchState{
      distRange = newMat initialRange,
      remainProfile = IntMap.fromDistinctAscList
        [ (i, profile) | i <- [0 .. n - 1]],
      blockers = initialBlockers
    }
    initialBlockers
      | isSingleton initialRange = Rel.empty
      | otherwise = Rel.fromList [
          (v, key) | (key, (i,j,k)) <- V.toList (V.indexed trigs), v <- [(i,j), (i,k), (j,k)]
        ]

getDistRange :: (Int,Int) -> SearchM Interval
getDistRange ij = gets (dGet ij . distRange)

dGet :: (Int,Int) -> SymMat Interval -> Interval
dGet (i,j) dm
  | i == j = I 0 0
  | otherwise = at (i,j) dm

putDistRange :: (Int,Int) -> Interval -> SearchM ()
putDistRange ij val = do
  modify' $ \st ->
    let !dist' = set ij val (distRange st)
    in st{ distRange = dist'}

enterAll :: [((Int,Int),Interval)] -> SearchM ()
enterAll [] = pure ()
enterAll (def : defs) = do
  newDefs <- enter def
  enterAll (newDefs ++ defs)

enter :: ((Int,Int),Interval) -> SearchM [((Int,Int),Interval)]
enter (ij, xRange) = do
  xRange0 <- getDistRange ij
  Just xRange' <- pure $ intersectInterval xRange xRange0
  if xRange' == xRange0
    then pure []
    else do
      putDistRange ij xRange'
      if isSingleton xRange'
        then do
          let I d _ = xRange'
          commit ij d
          unblock ij
        else pure []

commit :: (Int,Int) -> Int -> SearchM ()
commit (i,j) d = do
  profs <- gets remainProfile
  let p = profs IntMap.! i
      q = profs IntMap.! j
  guard $ IMS.member d p
  guard $ IMS.member d q
  let p' = IMS.delete d p
      q' = IMS.delete d q
      profs' = IntMap.insert i p' (IntMap.insert j q' profs)
  modify' $ \st -> st{ remainProfile = profs' }

keyToTriangle :: Int -> SearchM Triangle
keyToTriangle key = asks (V.! key)

unblock :: (Int,Int) -> SearchM [((Int,Int), Interval)]
unblock unblockEdge = do
  blockers0 <- gets blockers
  let updatedConstraints = Rel.lookup unblockEdge blockers0
  updateResults <- forM (Set.toList updatedConstraints) $ \key -> do
    (i,j,k) <- keyToTriangle key
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
    let changes =
             [ ((i,j),xRange'), ((i,k),yRange'), ((j,k),zRange') ]
        resolved = triangleInequalityAlways (xRange', yRange', zRange')
        key' | resolved = Nothing
             | otherwise = Just key
    pure (key', changes)
  let newBlockers = Rel.fromList [ (edge, key)
        | (Just key, changes) <- updateResults,
          (edge, range) <- changes,
          not (isSingleton range) ]
      allChanges = updateResults >>= snd
      blockers' = Rel.union (Map.delete unblockEdge blockers0) newBlockers
  modify' $ \st -> st{ blockers = blockers'}
  pure allChanges

choose :: (Foldable t, MonadPlus m) => t a -> m a
choose = foldr (\a r -> pure a `mplus` r) mzero

guess :: (Int,Int) -> SearchM Int
guess (i,j) = do
  profs <- gets remainProfile
  let p = profs IntMap.! i
      q = profs IntMap.! j
      candidates = IntSet.intersection (IMS.toSet p) (IMS.toSet q)
  choose $ IntSet.toList candidates 

solveLoop :: SearchM ()
solveLoop = do
  blockers0 <- gets blockers
  case getLargestBlocker blockers0 of
    Just ij -> do
      d <- guess ij
      enterAll [(ij, I d d)]
      solveLoop
    Nothing -> pure ()

getLargestBlocker :: Blocker -> Maybe (Int,Int)
getLargestBlocker b = case blockerList of
  [] -> Nothing
  (ij, _) : _ -> Just ij
  where
    blockerList = sortOn (Down . Set.size . snd) $ Map.toList b

-- Triangle inequality unconditionally hold for the given range
triangleInequalityAlways :: (Interval, Interval, Interval) -> Bool
triangleInequalityAlways (I xLo xHi, I yLo yHi, I zLo zHi) =
  -- Precondition: (0 <= xLo <= xHi), (0 <= yLo <= yHi), (0 <= zLo <= zHi)
  gap <= xLo && xHi <= top
  where
    -- gap = maximum [ abs (y - z) | y <- [yLo .. yHi], z <- [zLo .. zHi] ]
    gap = max (abs (yHi - zLo)) (abs (zHi - yLo))
    -- top = minimum [ y + z | y <- [yLo .. yHi], z <- [zLo .. zHi] ]
    top = yLo + zLo

narrow :: (Interval, Interval, Interval) -> Maybe (Interval, Interval, Interval)
narrow (xs, ys, zs) =
  (,,) <$> narrowOne (xs, ys, zs)
       <*> narrowOne (ys, zs, xs)
       <*> narrowOne (zs, xs, ys)

-- Narrow x range using triangle inequality
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

-- example profiles
squareProf, rectProf, cubeProf, cube4Prof :: [Int]
squareProf = [1,1,2]
rectProf = [1,2,3]
cubeProf = replicate 3 1 ++ replicate 3 2 ++ [3]
cube4Prof = replicate 4 1 ++ replicate 6 2 ++ replicate 4 3 ++ [4]

----

-- "Frozen" distance matrix
data DM = MkDM Int (UV.Vector Int)
  deriving (Eq, Ord, Show)

makeDM :: Int -> SymMat Interval -> DM
makeDM n dm = MkDM n $ UV.fromListN (triangular (n - 1)) dmContent
  where
    dmContent = do
      j <- [0 .. n - 1]
      i <- [0 .. j - 1]
      let I lo hi = at (i,j) dm
      assert (lo == hi) $ pure lo

-- | Convert to table for pretty-printing
prettyTable :: DM -> Table
prettyTable (MkDM n vec) = Table n n f
  where
    f i j
      | i == j = "0"
      | otherwise = show $ vec UV.! (min i j + triangular (max i j - 1))

transposeDM :: Int -> Int -> Int -> DM -> DM
transposeDM n s t
  | s < 0 || t < 0 || s >= n || t >= n = error $ "out of bounds: " ++ show (n,s,t)
  | s == t = id
  | otherwise = apply
  where
    tr k
      | k == s = t
      | k == t = s
      | otherwise = k
    perm = UV.fromListN (triangular (n - 1)) permList
    permList = do
      j <- [0 .. n - 1]
      i <- [0 .. j - 1]
      let i' = tr i
          j' = tr j
      pure $ min i' j' + triangular (max i' j' - 1)
    
    apply (MkDM n' vec)
      | n /= n' = error $ "applying to DM of wrong size: " ++ show (n,n')
      | otherwise = MkDM n $ UV.backpermute vec perm
