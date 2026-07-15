{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Math.ContingencyTable(
  Table(..),

  contingencyTables,
  uniqueContingencyTables,
  pointedContingencyTables,
  uniquePointedContingencyTables,

  pprTable,
  latexTable
) where

import qualified Data.Vector.Unboxed as UV

import Math.Combinatorics ( partitionsK, IntBag, subIntBags )
import EquivalenceUtil ( uniqueUpTo )
import qualified Data.IntMultiSet as IntBag

import qualified Text.Table as Text

-- |
--
-- > UV.length sumRows == numRows
-- > UV.length sumCols == numCols
-- > UV.length entries == numRows * numCols
data Table a = MkTable
  { numRows :: Int,
    numCols :: Int,
    -- | row-major
    entries :: UV.Vector a
  }
  deriving (Show, Eq, Ord)

vecToIntBag :: UV.Vector Int -> IntBag
vecToIntBag v = IntBag.fromOccurList
  [ (k,n) | (k,n) <- zip [0..] (UV.toList v), n > 0 ]

vecFromIntBag :: Int -> IntBag -> UV.Vector Int
vecFromIntBag len bag = UV.generate len (\k -> IntBag.occur k bag)

tablesFromMarginal :: UV.Vector Int -> UV.Vector Int -> [Table Int]
tablesFromMarginal rows cols
  | UV.sum rows /= UV.sum cols = error "Total sum doesn't match"
  | otherwise = makeTable <$> genEntries (UV.toList rows) (vecToIntBag cols)
  where
    nrows = UV.length rows
    ncols = UV.length cols
    bagToRowList = UV.toList . vecFromIntBag ncols
    makeTable e =
      MkTable
        { numRows = nrows,
          numCols = ncols,
          entries = UV.fromList $ e >>= bagToRowList
        }

    genEntries :: [Int] -> IntBag -> [[IntBag]]
    genEntries [] _ = [[]]
    genEntries (r : rs) caps = do
      (d, caps') <- subIntBags r caps
      ds <- genEntries rs caps'
      pure (d : ds)

generateContingencyTables :: Int -> Int -> Int -> [(UV.Vector Int, UV.Vector Int, [Table Int])]
generateContingencyTables h w n =
  do
    rows <- UV.fromList <$> partitionsK n h
    cols <- UV.fromList <$> partitionsK n w
    pure (rows, cols, tablesFromMarginal rows cols)

newtype Shuffle = Shuffle (UV.Vector Int)
  deriving (Show, Eq)

applyShuffle :: UV.Unbox a => Shuffle -> Table a -> Table a
applyShuffle (Shuffle s) (MkTable rows cols xs) = (MkTable rows cols (UV.backpermute xs s))

-- Generator of permutation groups of indices preserving "runs" (contigent range of indices with equal value)
safeSwaps :: Eq k => [k] -> [Int -> Int]
safeSwaps [] = []
safeSwaps ks@(_:ks') = makeSwap <$> swapPositions
  where
    swapPositions = [ i | (i,k,k') <- zip3 [0..] ks ks', k == k']
    makeSwap i j 
      | i == j     = i + 1
      | i + 1 == j = i
      | otherwise  = j

tableShuffles :: UV.Vector Int -> UV.Vector Int -> [Shuffle]
tableShuffles rows cols = rowShuffles ++ colShuffles
  where
    h = UV.length rows
    w = UV.length cols
    rowShuffles = do
      rowSwap <- safeSwaps (UV.toList rows)
      let ixes = UV.fromListN (h * w) [rowSwap i * w + j | i <- [0 .. h - 1], j <- [0 .. w - 1]]
      pure (Shuffle ixes)
    colShuffles = do
      colSwap <- safeSwaps (UV.toList cols)
      let ixes = UV.fromListN (h * w) [i * w + colSwap j | i <- [0 .. h - 1], j <- [0 .. w - 1] ]
      pure (Shuffle ixes)

contingencyTables :: Int -> Int -> Int -> [Table Int]
contingencyTables h w n = generateContingencyTables h w n >>= \(_, _, tabs) -> tabs

uniqueContingencyTables :: Int -> Int -> Int -> [Table Int]
uniqueContingencyTables h w n =
  generateContingencyTables h w n >>= \(rows, cols, tabs) ->
    uniqueUpTo (applyShuffle <$> tableShuffles rows cols) tabs

generatePointedContingencyTables :: Int -> Int -> Int -> [(UV.Vector Int, UV.Vector Int, [Table Int])]
generatePointedContingencyTables h w n =
  do
    ptRow <- [n, n - 1 .. 0]
    freeRows <- partitionsK (n - ptRow) h
    let rows = UV.fromList (ptRow : freeRows)
    ptCol <- [n, n - 1 .. 0]
    freeCols <- partitionsK (n - ptCol) w
    let cols = UV.fromList (ptCol : freeCols)
    pure (rows, cols, tablesFromMarginal rows cols)

pointedContingencyTables :: Int -> Int -> Int -> [Table Int]
pointedContingencyTables h w n = generatePointedContingencyTables h w n >>= \(_, _, tabs) -> tabs

uniquePointedContingencyTables :: Int -> Int -> Int -> [Table Int]
uniquePointedContingencyTables h w n =
  generatePointedContingencyTables h w n >>= \(rows, cols, tabs) ->
    let -- Set the duplicity of the first element (the pointed part) to -1.
        -- The actual duplicity doesn't matter and doesn't want it to move.
        rows' = rows UV.// [(0, -1)]
        cols' = cols UV.// [(0, -1)]
     in uniqueUpTo (applyShuffle <$> tableShuffles rows' cols') tabs

-- * Pretty printing

toTextTable :: (UV.Unbox a, Show a) => Table a -> Text.Table
toTextTable (MkTable h w tab) = Text.Table h w $ \i j -> show (tab UV.! (i * w + j))

pprTable :: (UV.Unbox a, Show a) => Table a -> String
pprTable = Text.prettyShowTable Text.defaultStyle . toTextTable
      
latexTable :: (UV.Unbox a, Show a) => Table a -> String
latexTable = Text.prettyShowTable Text.latexStyle . toTextTable