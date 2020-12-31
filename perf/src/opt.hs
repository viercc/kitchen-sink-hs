import Runner

main :: IO ()
main = runWork isSquare

isSquare :: (Num a, Ord a) => a -> Bool
isSquare n = go 1 0
  where
    go k m = k `seq` m `seq` case compare m n of
      LT -> go (k + 2) (m + k)
      EQ -> True
      GT -> False
{-# SCC isSquare #-}
