import Runner

main :: IO ()
main = runWork isSquare

{-
-- With and without optimization, adding annotation
isSquare :: (Num a, Enum a, Ord a) => a -> Bool
-- made no impact on performance
-}
isSquare n = n == c * c
  where
    c = head $ dropWhile (\m -> m * m < n) [0..]
{-# SCC isSquare #-}
