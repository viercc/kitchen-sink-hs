import Control.Monad (join)
import Runner

main :: IO ()
main = runWork isSquare

squares = map (join (*)) [0..]

isSquare n = foldr alg (error "squares: finite!") squares
 where
  alg m r = case compare m n of
   LT -> r
   EQ -> True
   GT -> False
{-# SCC isSquare #-}
