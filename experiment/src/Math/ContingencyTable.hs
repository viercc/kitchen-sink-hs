{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Math.ContingencyTable(
  Table(..), tableContents,

  contingencyTables,
  uniqueContingencyTables,
  pointedContingencyTables,
  uniquePointedContingencyTables,

  pprTable,
  latexTable
) where

import Data.List (intercalate)
import qualified Data.Vector.Unboxed as UV

import Math.Combinatorics
import EquivalenceUtil

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

tableContents :: Table -> [[Int]]
tableContents table =
    [[ tab UV.! (i * w + j) | j <- [0 .. w - 1]] | i <- [0 .. h - 1]]
  where
    h = numRows table
    w = numCols table
    tab = entries table

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

applyShuffle :: UV.Unbox a => Shuffle -> UV.Vector a -> UV.Vector a
applyShuffle (Shuffle s) xs = UV.backpermute xs s

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
    modTables = uniqueUpTo (applyShuffle <$> shuffles) bareTables
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

-- * Pretty printing

padStringTable :: [[String]] -> [[String]]
padStringTable strCells = zipWith leftPad cellWidths <$> strCells
  where
    leftPad n s = replicate (n - length s) ' ' ++ s
    cellWidths = foldr (zipWith max . fmap length) (repeat 0) strCells

pprTable :: Table -> String
pprTable
  = unlines . fmap unwords . padStringTable . fmap (fmap show) . tableContents

latexTable :: Table -> String
latexTable
  = intercalate " \\\\ " . fmap (intercalate " & ") . padStringTable . fmap (fmap show) . tableContents
