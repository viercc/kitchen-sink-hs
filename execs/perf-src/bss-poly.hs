import Control.Monad (join)
import Runner

main :: IO ()
main = runWork isSquare

squares :: (Num a, Enum a) => [a]
squares = map (join (*)) [0..]

isSquare :: (Num a, Enum a, Ord a) => a -> Bool
isSquare n = foldr alg (error "squares: finite!") squares
 where
  alg m r = case compare m n of
   LT -> r
   EQ -> True
   GT -> False
{-# SCC isSquare #-}
