{-# LANGUAGE GADTs          #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
module Main where

import Type.Reflection
import Data.HMatchable
import Universe

main :: IO ()
main = do
  -- match on Int
  printPatternMatch (lit 1) (var "x")
  printPatternMatch (lit 1) (litPat 1)
  printPatternMatch (lit 1) (litPat 2)

  -- match on [Int]
  printPatternMatch @[Int] nil nilPat
  printPatternMatch @[Int] nil (consPat (var "x") (var "xs"))
  printPatternMatch @[Int] (list (lit <$> [1])) (consPat (var "x") (var "xs"))
  printPatternMatch @[Int] (list (lit <$> [1,2,3])) (consPat (var "x") (var "xs"))

  -- match on [[Int]]
  printPatternMatch @[[Int]] nil (var "xss")
  printPatternMatch @[[Int]] (list [nil, cons (lit 1) nil]) (consPat nilPat (consPat (consPat (var "x") nilPat) (var "xss")))

  -- match on (Int, [Int])
  printPatternMatch (pair (lit 1) (list (lit <$> [3,4,5]))) (pairPat (var "x") (var "ys"))
  printPatternMatch (pair (lit 1) (list (lit <$> [3,4,5]))) (pairPat (var "x") (consPat (var "y") (var "ys")))

printPatternMatch :: Value a -> Pattern a -> IO ()
printPatternMatch val pat = do
  putStrLn $ "== match {" ++ prettyVal val ++ "} {" ++ prettyPat pat ++ "}"
  case hPatternMatch pat val of
    Nothing -> do putStrLn "  Fail"
    Just as -> do putStrLn "  Success"
                  mapM_ (\a -> putStrLn ("    " ++ prettyAssignment a)) as

var :: Typeable a => String -> Pattern a
var varName = varPat (varName :::: typeRep)
