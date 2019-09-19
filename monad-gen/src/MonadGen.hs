{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE DerivingVia               #-}
module Main where

import           Data.Foldable
import           GHC.Generics

import           Control.Monad       (guard)
import           Control.Monad.State (evalState, state)

import           Vec
import           Enum1

------------------------
-- Tests

skolem :: (Traversable m, Enum1 m) => Vec (m Int)
skolem = fmap fillIn $ enum1 $ vec [state (\i -> (i, i+1))]
  where fillIn mx = evalState (sequenceA mx) 0

skolem2 :: (Traversable m, Enum1 m) => Vec (m (m Int))
skolem2 = fmap fillIn $ enum1 $ enum1 $ vec [state (\i -> (i, i+1))]
  where sequenceTwice = traverse sequenceA
        fillIn mmx = evalState (sequenceTwice mmx) 0

skolem3 :: (Traversable m, Enum1 m) => Vec (m (m (m Int)))
skolem3 = fmap fillIn $ enum1 $ enum1 $ enum1 $ vec [state (\i -> (i, i+1))]
  where sequenceThrice = traverse (traverse sequenceA)
        fillIn mmmx = evalState (sequenceThrice mmmx) 0

checkLeftUnit :: (Traversable m, Enum1 m, Eq (m Int)) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m Int -> Bool
checkLeftUnit pure' join' ma = join' (pure' ma) == ma

checkRightUnit :: (Traversable m, Enum1 m, Eq (m Int)) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m Int -> Bool
checkRightUnit pure' join' ma = join' (fmap pure' ma) == ma

checkAssoc :: (Traversable m, Enum1 m, Eq (m Int)) =>
  (forall a. m (m a) -> m a) -> m (m (m Int)) -> Bool
checkAssoc join' mmma = join' (join' mmma) == join' (fmap join' mmma)

counterExamplesAssoc :: (Traversable m, Enum1 m, Eq (m Int)) =>
  (forall a. m (m a) -> m a) -> [m (m (m Int))]
counterExamplesAssoc join' =
  [ mmma | mmma <- toList skolem3, join' (join' mmma) /= join' (fmap join' mmma)]

cache :: Vec a -> Vec a
cache = fromVector . toVector

--data F a = F0 a | F1 a a
data F a = F0 | F1 a | F2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically F)

puresF :: Vec (a -> F a)
puresF = allPures

joinsF :: Vec (F (F a) -> F a)
joinsF = allJoins

okayPairs :: [(Int, Int)]
okayPairs =
  do i <- [0 .. length puresF - 1]
     j <- [0 .. length joinsF - 1]
     let pure' :: a -> F a
         pure' = puresF ! i

         join' :: F (F a) -> F a
         join' = joinsF ! j
     guard $ all (checkLeftUnit pure' join') skolemCache
     guard $ all (checkRightUnit pure' join') skolemCache
     guard $ all (checkAssoc join') skolem3Cache
     return (i,j)
  where
    skolemCache :: Vec (F Int)
    skolemCache = cache skolem

    skolem3Cache :: Vec (F (F (F Int)))
    skolem3Cache = cache skolem3

printJoinTable :: Int -> IO ()
printJoinTable i =
  let f = joinsF ! i
      makeEntry ffx = (show ffx, show (f ffx))
      table = fmap makeEntry skolem2
      maxLenArg = maximum $ fmap (length . fst) table
      format (x,y) = x ++ replicate (maxLenArg - length x) ' ' ++ " -> " ++ y
  in for_ table $ \entry -> putStrLn (format entry)

main :: IO ()
main =
  do putStrLn $ "#pure = #(forall a. a -> F a) = " ++ show (length puresF)
     putStrLn $ "#join = #(forall a. F (F a) -> F a) = " ++ show (length joinsF)
     for_ okayPairs $ \(i,j) -> do
       putStrLn "--------------------------------------------"
       print (i,j)
       printJoinTable j
