module Combinatorics where

import Data.Function (on)
import Data.List (groupBy, permutations)
import Data.Monoid (Ap (..))
import qualified Data.Set as Set
import qualified Data.Vector.Unboxed as UV

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

-- | Enumerate partitions of @n@ of to @k@ natural numbers.
--
-- * Unique up to reordering. e.g. [1,2,0] and [2,1,0] are considered equal
-- * A returned partition is represented as a list of positive integers in descending order
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

generateContigencyTables :: Int -> Int -> Int -> [(UV.Vector Int, UV.Vector Int, [Table])]
generateContigencyTables h w n =
  do
    rows <- UV.fromList <$> partitionsK n h
    cols <- UV.fromList <$> partitionsK n w
    pure (rows, cols, tablesFromMarginal rows cols)

newtype Shuffle = Shuffle (UV.Vector Int)
  deriving (Show, Eq)

applyShuffle :: UV.Unbox a => UV.Vector a -> Shuffle -> UV.Vector a
applyShuffle xs (Shuffle s) = UV.backpermute xs s

-- Shuffle of indices, which fixes "groups" (contigent range of indices with equal value)
shufflesFixingDup :: [Int] -> [Shuffle]
shufflesFixingDup xs = fmap (Shuffle . UV.fromList) . getAp $ foldMap (Ap . permutations) indexGroups
  where
    indexGroups =
      do
        grp <- groupBy ((==) `on` fst) (zip xs [0 ..])
        if fst (head grp) == 0
          then map (\(_, i) -> [i]) grp
          else [map snd grp]

tableShuffles :: UV.Vector Int -> UV.Vector Int -> [Shuffle]
tableShuffles rows cols = entryIxes
  where
    w = UV.length cols
    entryIxes = do
      Shuffle rowIxes <- shufflesFixingDup (UV.toList rows)
      Shuffle colIxes <- shufflesFixingDup (UV.toList cols)
      let ixes = UV.fromList [i * w + j | i <- UV.toList rowIxes, j <- UV.toList colIxes]
      pure (Shuffle ixes)

contigencyTables :: Int -> Int -> Int -> [Table]
contigencyTables h w n = generateContigencyTables h w n >>= \(_, _, tabs) -> tabs

uniqueContigencyTables :: Int -> Int -> Int -> [Table]
uniqueContigencyTables h w n =
  generateContigencyTables h w n >>= \(rows, cols, tabs) ->
    uniqueTableModulo (tableShuffles rows cols) tabs

uniqueTableModulo :: [Shuffle] -> [Table] -> [Table]
uniqueTableModulo shuffles = loop Set.empty
  where
    loop _ [] = []
    loop visited (tab : rest)
      | Set.member (entries tab) visited = loop visited rest
      | otherwise =
          let newTabs = applyShuffle (entries tab) <$> shuffles
              visited' = Set.union visited (Set.fromList newTabs)
           in tab : loop visited' rest

generatePointedContigencyTables :: Int -> Int -> Int -> [(UV.Vector Int, UV.Vector Int, [Table])]
generatePointedContigencyTables h w n =
  do
    ptRow <- [n, n - 1 .. 0]
    freeRows <- partitionsK (n - ptRow) h
    let rows = UV.fromList (ptRow : freeRows)
    ptCol <- [n, n - 1 .. 0]
    freeCols <- partitionsK (n - ptCol) w
    let cols = UV.fromList (ptCol : freeCols)
    pure (rows, cols, tablesFromMarginal rows cols)

pointedContigencyTables :: Int -> Int -> Int -> [Table]
pointedContigencyTables h w n = generatePointedContigencyTables h w n >>= \(_, _, tabs) -> tabs

uniquePointedContigencyTables :: Int -> Int -> Int -> [Table]
uniquePointedContigencyTables h w n =
  generatePointedContigencyTables h w n >>= \(rows, cols, tabs) ->
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
