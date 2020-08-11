module Summation where

import Data.List (sortBy)
import Data.Ord (comparing)
import qualified Data.Vector.Unboxed as V

type Query = (Int, Int, Int)

test1 :: [Query]
test1 =
  [ (1,2,100)
  , (2,5,100)
  , (3,4,100)
  ]

test2 :: [Query]
test2 = 
  [ (1,   2000,100)
  , (1001,5000,100)
  , (2001,4000,100)
  ]

-- | cumulative summation
--
-- > cumsum [x,y,z] = [0, x, x + y, x + y + z]
cumsum :: Num a => [a] -> [a]
-- cumsum = scanl (+) 0
cumsum = go 0
  where
    go acc [] = [acc]
    go acc (x:xs) = acc `seq` (acc : go (acc + x) xs)

-- | This is what I called O(m * log m)
summationOrd :: Int -> [Query] -> Int
summationOrd _ queries =
  maximum . cumsum . map snd . sortBy (comparing fst) $
    do (start, end, summand) <- queries
       [ (start, summand), (end+1, negate summand) ]


-- | This is what I called O(n + m)
summationVec :: Int -> [Query] -> Int
summationVec n queries = maximum . cumsum $ V.toList arr
  where
    zeroes = V.replicate (n+1) 0
    arr = V.accum (+) zeroes $
      do (start, end, summand) <- queries
         [ (start-1, summand), (end, negate summand) ]

