module Main where

import System.Random
import Control.Monad (replicateM)

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Map qualified as Map

import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Diagrams
import Data.List (intercalate)
import Control.Applicative

main :: IO ()
main = do
    pointsList <- randomPoints 40 10 10
    let points = Set.fromList pointsList
        namedPoints = Map.fromList (zip (Set.toList points) [1 :: Int ..])
        showPathByName ps = case traverse (\p -> Map.lookup p namedPoints) ps of
            Nothing -> "????????"
            Just namePath -> show namePath
    mapM_ print (Map.toList namedPoints)
    mapM_ (putStrLn . showPathByName . take 3) (allTabooPaths points)

randomPoint :: Double -> Double -> IO (Double, Double)
randomPoint w h = (,) <$> randomRIO (0,w) <*> randomRIO (0,h)

randomPoints :: Int -> Double -> Double -> IO [(Double, Double)]
randomPoints n w h = replicateM n (randomPoint w h)

hypot :: Double -> Double -> Double
hypot 0 y = abs y
hypot x 0 = abs x
hypot x y
  | x == 0       = y_
  | y == 0       = x_
  | isInfinite x || isInfinite y = 1/0 -- +Infinity
  | isNaN x || isNaN y = 0/0           -- NaN
  | x_ <= y_     = hypot' x_ y_
  | otherwise    = hypot' y_ x_
  where
    x_ = abs x
    y_ = abs y
    -- 0 < a <= b
    hypot' a b =
        -- To make sure the overflow doesn't happen,
        -- scale a,b so that 0 < 2^(-i)*a <= 2^(-i)*b <= 1 
        let i = exponent b
            a' = scaleFloat (-i) a
            b' = scaleFloat (-i) b
        in scaleFloat i (sqrt (a' * a' + b' * b'))

dist :: (Double,Double) -> (Double,Double) -> Double
dist (x1, y1) (x2, y2) = hypot (x1 - x2) (y1 - y2)

mergeOn :: (Ord b) => (a -> b) -> [a] -> [a] -> [a]
mergeOn f = go where
    go [] ys = ys
    go xs [] = xs
    go (x:xs) (y:ys) 
       | f x <= f y = x : go xs (y:ys)
       | otherwise  = y : go (x:xs) ys

nearestPoint :: Set (Double,Double) -> (Double,Double) -> (Double,Double)
nearestPoint s q = go points
  where
    (preSet, postSet) = Set.spanAntitone (< q) s
    pre  = [ (distX p, p) | p <- Set.toDescList preSet ]
    post = [ (distX p, p) | p <- Set.toAscList postSet ]
    points = mergeOn fst pre post
    
    distX p = abs (fst p - fst q)

    go [] = error "must be nonempty set"
    go ((_,p):ps') = go2 (dist p q) p ps'
    go2 bestDist best ps = case ps of
        [] -> best
        (dx,p):ps'
          | bestDist <= dx -> best
          | otherwise ->
               let d = dist p q
               in if d <= bestDist
                     then go2 d p ps'
                     else go2 bestDist best ps'

allTabooPaths :: Set (Double,Double) -> [[(Double,Double)]]
allTabooPaths s = [ tabooPathFrom s p | p <- Set.toList s ]

tabooPathFrom :: Set (Double,Double) -> (Double,Double) -> [(Double,Double)]
tabooPathFrom s p
  | Set.size s <= 1 = [p]
  | otherwise = p : tabooPathFrom s' q
      where
        s' = Set.delete p s
        q = nearestPoint s' p
