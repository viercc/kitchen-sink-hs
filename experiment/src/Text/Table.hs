module Text.Table where

import qualified Data.Vector.Strict as V
import Data.List (intercalate)

data Table = Table { tableRows :: Int, tableCols :: Int, tableContent :: Int -> Int -> String }

data TablePrettyStyle = TablePrettyStyle {
    columnSep :: String,
    rowSep :: String,
    cellAlign :: CellAlign,
    minColumnWidth :: Int
  }
  deriving (Show, Read, Eq)

data CellAlign = AlignRight | AlignLeft
  deriving (Show, Read, Eq)

defaultStyle, latexStyle :: TablePrettyStyle
defaultStyle = TablePrettyStyle {
  columnSep = " ",
  rowSep = "\n",
  cellAlign = AlignRight,
  minColumnWidth = 0
}

latexStyle = TablePrettyStyle {
  columnSep = " & ",
  rowSep = "\\\n",
  cellAlign = AlignRight,
  minColumnWidth = 0
}

prettyShowTable :: TablePrettyStyle -> Table -> String
prettyShowTable style (Table trows tcols f) = intercalate (rowSep style) (V.toList (prettyRow <$> tab))
  where
    tab = V.generate trows $ \i ->
      V.generate tcols $ \j ->
        let s = f i j
        in (length s, s)
    defaultColWidths = V.replicate tcols (minColumnWidth style)
    colWidths = V.foldl' (V.zipWith (\w (n,_) -> max w n)) defaultColWidths tab
    prettyRow row = intercalate (columnSep style) $ V.toList (V.zipWith prettyCell colWidths row)
    prettyCell = case cellAlign style of
      AlignRight -> alignRight
      AlignLeft -> alignLeft
    alignRight w (n, s) = replicate (w - n) ' ' ++ s
    alignLeft  w (n, s) = s ++ replicate (w - n) ' '

instance Show Table where
  show = prettyShowTable defaultStyle
