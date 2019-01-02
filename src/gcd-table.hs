module Main where

import           Data.Foldable (for_)
import           System.IO

import           Data.List     (intercalate)
import qualified Data.Map      as Map
import qualified Data.Set      as Set

data Table r c a = Table [r] [c] [[a]]
                 deriving (Show, Eq, Ord)

instance Functor (Table r c) where
  fmap f (Table rows cols cells) = Table rows cols ((fmap . fmap) f cells)

tabulate :: [r] -> [c] -> (r -> c -> a) -> Table r c a
tabulate rows cols f =
  Table rows cols [ fmap (f r) cols | r <- rows ]

toCSV :: (Show r, Show c, Show a, Monad m) =>
         (String -> m ()) -> Table r c a -> m ()
toCSV puts (Table rows cols cells) =
  do puts $ commaSep ("" : fmap show cols)
     for_ (zip rows cells) $ \(r,as) ->
       puts $ commaSep (show r : fmap show as)

printCSV :: (Show r, Show c, Show a) => Table r c a -> IO ()
printCSV = toCSV putStrLn

writeCSV :: (Show r, Show c, Show a) => FilePath -> Table r c a -> IO ()
writeCSV file table =
  withFile file WriteMode (\h -> toCSV (hPutStrLn h) table)

commaSep :: [String] -> String
commaSep = intercalate ","

valTableFile, colMapFile, colTableFile :: FilePath
valTableFile = "gcd_vals.csv"
colMapFile   = "gcd_colormap.csv"
colTableFile = "gcd_color.csv"

main :: IO ()
main = do
  let f :: Int -> Int -> Integer
      f i j | i == j    = 0
            | otherwise = gcd (3^i + 2) (3^j + 2)
      n = 100
      tab = tabulate [1..n] [1..n] f
      rangeSet = case tab of (Table _ _ cells) -> Set.fromList (concat cells)
      colorMap = zip (Set.toAscList rangeSet) [(0::Integer)..]
      colorTab = let cm = Map.fromList colorMap in fmap (cm Map.!) tab
  writeCSV valTableFile tab
  withFile colMapFile WriteMode $ \h ->
    for_ colorMap $ \(x,c) ->
      hPutStrLn h $ show x ++ "," ++ show c
  writeCSV colTableFile colorTab
