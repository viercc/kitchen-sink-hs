{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
module Main(main) where

import Control.Applicative

import Monad.RStore
import MonadLaws
import System.Exit

import Data.Ord (comparing)
import Data.List (minimumBy, maximumBy)
import Data.Functor.Classes (Show1(..), showsUnaryWith, showsPrec1)
import Data.Foldable (for_)

tested :: Bool -> IO ()
tested True = return ()
tested False = exitFailure

data Q' a = Q' {
    constructorName :: String,
    constructorArgs :: [a],
    unwrap :: Q Int a
  }

instance Show1 Q' where
  liftShowsPrec showsPrecA showListA p (Q' con xs _) = showsUnaryWith (\_ ys -> showListA ys) con p xs

instance Show a => Show (Q' a) where
  showsPrec = showsPrec1

enumQ :: Enum1 Q'
enumQ var =
      qConst <$> var
  <|> qSlip <$> var <*> var
  <|> qPickMin <$> sequenceA [var, var]
  <|> qPickMax <$> sequenceA [var, var]
  <|> qDiff <$> var <*> var

qConst :: a -> Q' a
qConst x = Q' "qConst" [x] $ Q $ \_ -> (x, 0)

qSlip :: a -> a -> Q' a
qSlip x y = Q' "qSlip" [x,y] $ Q $ \f -> (x, f y)

qPickMin, qPickMax :: [a] -> Q' a
qPickMin xs = Q' "qPickMin" xs $ Q $ \f -> minimumBy (comparing snd) [ (x, f x) | x <- xs ]
qPickMax xs = Q' "qPickMax" xs $ Q $ \f -> maximumBy (comparing snd) [ (x, f x) | x <- xs ]

qDiff :: a -> a -> Q' a
qDiff x y =
  let qx = Q $ \f ->
        let d = f x - f y
        in if d < 0 then (y, d) else (x, d)
  in Q' "qDiff" [x,y] qx

data Fn x = IdFn | ConstFn x | BranchFn x (Fn x) (Fn x)

runFn :: (Ord x) => Fn x -> x -> x
runFn IdFn x = x
runFn (ConstFn c) _ = c
runFn (BranchFn b f1 f2) x = if x < b then runFn f1 x else runFn f2 x

showFn :: (Show x) => Fn x -> String
showFn = ("\\x -> " ++) . fnBody 0
  where
    fnBody _ IdFn = "x"
    fnBody _ (ConstFn c) = show c
    fnBody p (BranchFn b f1 f2) =
      let body = "if x < b then " ++ fnBody 1 f1 ++ " else " ++ fnBody 1 f2
      in if p > 0 then "(" ++ body ++ ")" else body

fnInts :: [Fn Int]
fnInts = genFnInts 3

genFnInts :: Int -> [Fn Int]
genFnInts n
  | n <= 0 = [IdFn, ConstFn 0, ConstFn 1 ]
  | otherwise = [ ConstFn n ] ++ [ IdFn ]
      ++ [ BranchFn b f1 f2 | b <- [ 2 ^ n ], f1 <- genFnInts (n - 2), f2 <- genFnInts (n - 1) ]

testEq :: Q Int Var -> Q Int Var -> Either (Fn Int) ()
testEq qx qy =
  for_ fnInts $ \fn ->
    let f = runFn fn
    in if runQ qx f == runQ qy f
         then Right ()
         else Left fn

main :: IO ()
main = printFailures allFailures >>= tested

data FailureCase =
    FailedLeftUnit (Q' Var) (Fn Int)
  | FailedRightUnit (Q' Var) (Fn Int)
  | FailedAssoc (Q' (Q' (Q' Var))) (Fn Int)

allFailures :: [ FailureCase ]
allFailures = leftUnitCases ++ rightUnitCases ++ assocCases
  where
    leftUnitCases = do
      qx' <- skolem1 enumQ
      let qx = unwrap qx'
      case testEq (pure qx >>= id) qx of
        Left fn -> [ FailedLeftUnit qx' fn ]
        Right _ -> []
    
    rightUnitCases = do
      qx' <- skolem1 enumQ
      let qx = unwrap qx'
      case testEq (qx >>= pure) qx of
        Left fn -> [ FailedRightUnit qx' fn ]
        Right _ -> []
    
    assocCases = do
      qqqx' <- skolem3 enumQ
      let qqqx = fmap (fmap unwrap) . fmap unwrap . unwrap $ qqqx'
      case testEq (qqqx >>= id >>= id) (qqqx >>= (>>= id)) of
        Left fn -> [ FailedAssoc qqqx' fn ]
        Right _ -> []

printFailures :: [ FailureCase ] -> IO Bool
printFailures failures = do
  for_ failures $ \case
    FailedLeftUnit qx fn -> do
      putStrLn "Counterexample for LeftUnit"
      putStrLn $ "  qx = " ++ show qx
      putStrLn "Evaluated at"
      putStrLn $ "  fn = " ++ showFn fn
    FailedRightUnit qx fn -> do
      putStrLn "Counterexample for RightUnit"
      putStrLn $ "  qx = " ++ show qx
      putStrLn "Evaluated at"
      putStrLn $ "  fn = " ++ showFn fn
    FailedAssoc qqqx fn -> do
      putStrLn "Counterexample for Assoc"
      putStrLn $ "  qqqx = " ++ show qqqx
      putStrLn "Evaluated at"
      putStrLn $ "  fn = " ++ showFn fn
  
  pure (null failures)