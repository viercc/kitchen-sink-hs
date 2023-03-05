module Main where

import Data.Foldable (for_)

import GHC.Arr

cardNum :: Int
cardNum = 15

numPairs :: Int
numPairs = (cardNum * (cardNum - 1)) `div` 2

goalMin, goalMax :: Double
goalMin = 1
goalMax = 100

lowerBoundForPair :: Int -> Int -> Maybe Double
lowerBoundForPair x y
  | x < y && t < 100 = Just (goalMax - fromIntegral t)
  | otherwise = Nothing
  where
    -- There are at least @s@ pairs smaller than or equal to (x,y)
    s = (x + 1) * (y + 1) - ((x + 1) * (x + 2)) `div` 2
    -- There are at most @t@ pairs greater than (x,y) 
    t = numPairs - s

upperBoundForPair :: Int -> Int -> Maybe Double
upperBoundForPair x y
  | x < y && t > 0 = Just (goalMin + fromIntegral t + 1)
  | otherwise      = Nothing
  where
    -- There are at least @s@ pairs greater than or equal to (x,y)
    x' = cardNum - x - 1
    y' = cardNum - y - 1
    s = (x' + 1) * (y' + 1) - ((y' + 1) * (y' + 2)) `div` 2
    -- There are at most @t@ pairs less than (x,y) 
    t = numPairs - s

varName :: Int -> String
varName i = "a" ++ show i;

minGap :: Double
minGap = log 1.01

main :: IO ()
main = do
  putStrLn $ "# number of cards = " ++ show cardNum
  putStrLn $ "var " ++ varName 0 ++ ";"
  for_ [1 .. cardNum - 1] $ \i ->
    putStrLn $ "var " ++ varName i ++ " >= " ++ show minGap ++ ";"
  for_ [0 .. cardNum - 1] $ \i ->
    for_ [i + 1 .. cardNum - 1] $ \j -> do
      let condName = "cond_" ++ show i ++ "_" ++ show j
          expr = showExpr [ (e, k) | k <- [0 .. j], let e = if k <= i then 2 else 1 ]
      printCond condName expr (lowerBoundForPair i j) (upperBoundForPair i j)

showExpr :: [(Int,Int)] -> String
showExpr = foldr (\(e,k) r -> show e ++ " * " ++ varName k ++ " + " ++ r) "0"

showLogOf :: Show a => a -> String
showLogOf x = "log(" ++ show x ++ ")"

printCond :: String -> String -> Maybe Double -> Maybe Double -> IO ()
printCond _ _ Nothing Nothing = pure ()
printCond condName expr Nothing (Just hi) =
    putStrLn $ "s.t. " ++ condName ++ " : " ++ expr ++ ", <= " ++ showLogOf hi ++ ";"
printCond condName expr (Just lo) Nothing =
    putStrLn $ "s.t. " ++ condName ++ " : " ++ showLogOf lo ++ ", <= " ++ expr ++ ";"
printCond condName expr (Just lo) (Just hi) =
    putStrLn $ "s.t. " ++ condName ++ " : " ++ showLogOf lo ++ ", <= " ++ expr ++ ", <= " ++ showLogOf hi ++ ";"
