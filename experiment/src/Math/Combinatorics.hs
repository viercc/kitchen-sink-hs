{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Math.Combinatorics where

import Data.List (intercalate)
import qualified Data.Vector.Unboxed as UV

import Data.Equivalence.Monad
import Data.Foldable (for_)

-- |
--
-- > UV.length sumRows == numRows
-- > UV.length sumCols == numCols
-- > UV.length entries == numRows * numCols
data Table = MkTable
  { numRows :: Int,
    numCols :: Int,
    -- | row-major
    entries :: UV.Vector Int
  }
  deriving (Show, Eq)

rowIndices :: Int -> Int -> [[Int]]
rowIndices h w = [[i * w + j | j <- [0 .. w - 1]] | i <- [0 .. h - 1]]

colIndices :: Int -> Int -> [[Int]]
colIndices h w = [[i * w + j | i <- [0 .. h - 1]] | j <- [0 .. w - 1]]

rowSums :: Table -> [Int]
rowSums MkTable {numRows = h, numCols = w, entries = tab} =
  fmap (sum . fmap (tab UV.!)) (rowIndices h w)

colSums :: Table -> [Int]
colSums MkTable {numRows = h, numCols = w, entries = tab} =
  fmap (sum . fmap (tab UV.!)) (colIndices h w)

-- | Enumerate partitions of @n@
--
-- - Unique up to reordering
-- - Descending order
partitions :: Int -> [[Int]]
partitions n0 = go n0 n0
  where
    go i n
      | n < 0 = []
      | n == 0 = [[]]
      | i <= 0 = []
      | i > n = go n n
      | otherwise =
          [i : rest | rest <- go i (n - i)]
            ++ go (i - 1) n

-- | Enumerate partitions of @n@ by @k@ natural numbers.
--
-- * Unique up to reordering. e.g. [1,2,3] and [2,1,3] are considered equal
-- * A returned partition is represented as a list of nonnegative integers in descending order
partitionsK :: Int -> Int -> [[Int]]
partitionsK n0 k0 = go k0 n0 n0
  where
    go k n m
      | k < 0 = []
      | n < m = go k n n
      | k * m < n = []
      | n == 0 = [replicate k 0]
      | k == 1 = [[n]]
      | otherwise = [m : xs | xs <- go (k - 1) (n - m) m] ++ go k n (m - 1)

-- | @distributions n k@ enumerates distributions of @n@ totals to @k@ integers
--
-- * The resulted numbers are ordered. e.g. [1,2,0] and [2,1,0] are
--   considered distinct distributions
distributions :: Int -> Int -> [[Int]]
distributions n k
  | n < 0 || k < 0 = []
  | n == 0 = [replicate k 0]
  | k == 1 = [[n]]
  | otherwise = do
      x <- [0 .. n]
      xs <- distributions (n - x) (k - 1)
      pure (x : xs)

-- | @subDistributions n as@ enumerates distributions @bs@ of @n@ totals to @k = length as@ integers,
--   under the restriction @bs !! i <= as !! i@ for all @i `elem` [0 .. k-1]@.
subDistributions :: Int -> [Int] -> [([Int], [Int])]
subDistributions n as = go n (sum as) as
  where
    go m _ [] = [([], []) | m == 0]
    go m t (a : as')
      | m > t = []
      | otherwise =
          -- (k <= a) && (m - k) <= (t - a)
          -- m + a - t <= k
          let minK = max 0 (m + a - t)
           in [(k : ks, (a - k) : rs) | k <- [minK .. a], (ks, rs) <- go (m - k) (t - a) as']

tablesFromMarginal :: UV.Vector Int -> UV.Vector Int -> [Table]
tablesFromMarginal rows cols
  | UV.sum rows /= UV.sum cols = error "Total sum doesn't match"
  | otherwise = makeTable <$> genEntries (UV.toList rows) (UV.toList cols)
  where
    makeTable e =
      MkTable
        { numRows = UV.length rows,
          numCols = UV.length cols,
          entries = UV.fromList (concat e)
        }

    genEntries [] _ = [[]]
    genEntries (r : rs) caps = do
      (d, caps') <- subDistributions r caps
      ds <- genEntries rs caps'
      pure (d : ds)

generateContingencyTables :: Int -> Int -> Int -> [(UV.Vector Int, UV.Vector Int, [Table])]
generateContingencyTables h w n =
  do
    rows <- UV.fromList <$> partitionsK n h
    cols <- UV.fromList <$> partitionsK n w
    pure (rows, cols, tablesFromMarginal rows cols)

newtype Shuffle = Shuffle (UV.Vector Int)
  deriving (Show, Eq)

applyShuffle :: UV.Unbox a => UV.Vector a -> Shuffle -> UV.Vector a
applyShuffle xs (Shuffle s) = UV.backpermute xs s

-- Generator of permutation groups of indices preserving "runs" (contigent range of indices with equal value)
shufflesFixingDup :: Eq k => [k] -> [Shuffle]
shufflesFixingDup ks = Shuffle . permutationVec <$> transpositions
  where
    n = length ks
    transpositions = [ i | (i,k,k') <- zip3 [0..] ks (tail ks), k == k']
    permutationVec i = UV.generate n $ \j -> case j of
      _ | i == j     -> i + 1
        | i + 1 == j -> i
        | otherwise  -> j

tableShuffles :: UV.Vector Int -> UV.Vector Int -> [Shuffle]
tableShuffles rows cols = rowShuffles ++ colShuffles
  where
    h = UV.length rows
    w = UV.length cols
    rowShuffles = do
      Shuffle rowIxes <- shufflesFixingDup (UV.toList rows)
      let ixes = UV.fromListN (h * w) [i * w + j | i <- UV.toList rowIxes, j <- [0 .. w - 1]]
      pure (Shuffle ixes)
    colShuffles = do
      Shuffle colIxes <- shufflesFixingDup (UV.toList cols)
      let ixes = UV.fromListN (h * w) [i * w + j | i <- [0 .. h - 1], j <- UV.toList colIxes ]
      pure (Shuffle ixes)

contingencyTables :: Int -> Int -> Int -> [Table]
contingencyTables h w n = generateContingencyTables h w n >>= \(_, _, tabs) -> tabs

uniqueContingencyTables :: Int -> Int -> Int -> [Table]
uniqueContingencyTables h w n =
  generateContingencyTables h w n >>= \(rows, cols, tabs) ->
    uniqueTableModulo (tableShuffles rows cols) tabs

uniqueTableModulo :: [Shuffle] -> [Table] -> [Table]
uniqueTableModulo _ [] = []
uniqueTableModulo shuffles tables = rebuildTable <$> modTables
  where
    bareTables = entries <$> tables
    modTables = runEquivM id min $ do
      for_ bareTables $ \tab -> equateAll (tab : map (applyShuffle tab) shuffles)
      classes >>= traverse desc
    h = numRows (head tables)
    w = numCols (head tables)
    rebuildTable = MkTable h w

generatePointedContingencyTables :: Int -> Int -> Int -> [(UV.Vector Int, UV.Vector Int, [Table])]
generatePointedContingencyTables h w n =
  do
    ptRow <- [n, n - 1 .. 0]
    freeRows <- partitionsK (n - ptRow) h
    let rows = UV.fromList (ptRow : freeRows)
    ptCol <- [n, n - 1 .. 0]
    freeCols <- partitionsK (n - ptCol) w
    let cols = UV.fromList (ptCol : freeCols)
    pure (rows, cols, tablesFromMarginal rows cols)

pointedContingencyTables :: Int -> Int -> Int -> [Table]
pointedContingencyTables h w n = generatePointedContingencyTables h w n >>= \(_, _, tabs) -> tabs

uniquePointedContingencyTables :: Int -> Int -> Int -> [Table]
uniquePointedContingencyTables h w n =
  generatePointedContingencyTables h w n >>= \(rows, cols, tabs) ->
    let -- Set the duplicity of the first element (the pointed part) to -1.
        -- The actual duplicity doesn't matter and doesn't want it to move.
        rows' = rows UV.// [(0, -1)]
        cols' = cols UV.// [(0, -1)]
     in uniqueTableModulo (tableShuffles rows' cols') tabs

pprTable :: Table -> String
pprTable MkTable {numRows = h, numCols = w, entries = tab} = unlines . fmap (unwords . zipWith leftPad cellWidths) $ strCells
  where
    leftPad n s = replicate (n - length s) ' ' ++ s
    strCells = fmap (fmap (show . (tab UV.!))) (rowIndices h w)
    cellWidths = foldr (zipWith max) (repeat 0) $ fmap (fmap length) strCells

latexTable :: Table -> String
latexTable MkTable {numRows = h, numCols = w, entries = tab} = intercalate " \\\\ " . fmap (intercalate " & " . zipWith leftPad cellWidths) $ strCells
  where
    leftPad n s = replicate (n - length s) ' ' ++ s
    strCells = fmap (fmap (show . (tab UV.!))) (rowIndices h w)
    cellWidths = foldr (zipWith max) (repeat 0) $ fmap (fmap length) strCells
