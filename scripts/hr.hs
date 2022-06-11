module Main where

import Data.Ord (comparing)
import Data.List (sortBy)

import Data.Array

-- https://www.hackerrank.com/challenges/permutation-equation/problem?isFullScreen=true

testInput :: [Int]
testInput = [5,2,1,3,4]

testOutput :: [Int]
testOutput = [4,2,5,1,3]

-- x ∘ y^(-1)
compInvPerm :: Int -> [Int] -> [Int] -> [Int]
compInvPerm n x y = elems $ array (1,n) (zip y x)

-- id ∘ x^(-1) ∘ x^(-1)
solve :: [Int] -> [Int]
solve x = compInvPerm n (compInvPerm n [1..n] x) x where
    n = length x

main :: IO ()
main = print (solve testInput)
