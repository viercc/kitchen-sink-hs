{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE DerivingVia               #-}
module Main(main) where

import           Data.Foldable
import           Data.Proxy
import           GHC.Generics

import           Control.Monad       (guard)
import           Control.Monad.State (evalState, state)

import           Data.Coerce

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

checkLeftUnit :: (Traversable m, Enum1 m, Eq (m b)) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m b -> Bool
checkLeftUnit pure' join' mb = join' (pure' mb) == mb

checkRightUnit :: (Traversable m, Enum1 m, Eq (m b)) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m b -> Bool
checkRightUnit pure' join' mb = join' (fmap pure' mb) == mb

checkAssoc :: (Traversable m, Enum1 m, Eq (m b)) =>
  (forall a. m (m a) -> m a) -> m (m (m b)) -> Bool
checkAssoc join' mmmb = join' (join' mmmb) == join' (fmap join' mmmb)

counterExamplesAssoc :: (Traversable m, Enum1 m, Eq (m Int)) =>
  (forall a. m (m a) -> m a) -> [m (m (m Int))]
counterExamplesAssoc join' =
  [ mmma | mmma <- toList skolem3, join' (join' mmma) /= join' (fmap join' mmma)]

cache :: Vec a -> Vec a
cache = fromVector . toVector

data F a = F0 | F2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically F)

data G a = G1 a | G2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically G)

data H a = H0 | H1 a | H2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically H)

data J a = J1_0 a | J1_1 a | J2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically J)

data T a = T2_0 a a | T2_1 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically T)

data W a = W1_0 a | W1_1 a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
  deriving (Enum1, CoEnum1) via (Generically W)

monadGen
  :: forall f.
       (forall a. Eq a => Eq (f a),
       forall a. Show a => Show (f a),
       Traversable f,
       Enum1 f)
       => Proxy f -> [String]
monadGen _ = header ++ (okayPairs >>= docResult)
  where
    puresF :: forall a. Vec (a -> f a)
    puresF = allPures
    
    joinsF :: forall a. Vec (Vec (f (f a) -> f a))
    joinsF = coerce $ steppedCoEnum1 @(f :.: f) @f @a
    
    skolemCache :: Vec (f Int)
    skolemCache = cache skolem
    
    skolem2Cache :: Vec (f (f Int))
    skolem2Cache = cache skolem2
    
    skolem3Cache :: Vec (f (f (f Int)))
    skolem3Cache = cache skolem3
    
    numAllJoins = sum [ length joins' | joins' <- toList joinsF ]
    header =
      [ "#pure = #(forall a. a -> F a) = " ++ show (length puresF)
      , "#join = #(forall a. F (F a) -> F a) = " ++ show numAllJoins
      , "#(F (F ()) -> F ()) = " ++ show (length joinsF)
      ]

    okayPairs :: [(Int, Int, Int)]
    okayPairs =
      do i <- [0 .. length puresF - 1]
         let pure' :: forall b. b -> f b
             pure' = puresF ! i
         j <- [0 .. length joinsF - 1]
         let n = length $ joinsF ! j
         guard $ n > 0
         let join0 :: forall b. f (f b) -> f b
             join0 = (joinsF ! j) ! 0
         guard $ all (checkLeftUnit pure' join0) (enum1 (singleton ()))
         guard $ all (checkRightUnit pure' join0) (enum1 (singleton ()))
         guard $ all (checkAssoc join0) (enum1 (enum1 (enum1 (singleton ()))))
         k <- [0 .. n - 1]
         let join' :: forall b. f (f b) -> f b
             join' = (joinsF ! j) ! k
         guard $ all (checkLeftUnit pure' join') skolemCache
         guard $ all (checkRightUnit pure' join') skolemCache
         guard $ all (checkAssoc join') skolem3Cache
         return (i,j,k)

    joinArgsCache :: Vec String
    joinArgsCache = cache $ fmap pad strs
      where showLen x = let s = show x in (length s, s)
            strs = cache $ showLen <$> skolem2Cache
            maxLen = maximum $ fmap fst strs
            pad (n, s) = "join $ " ++ s ++ replicate (maxLen - n) ' ' ++ " = "

    
    docResult (i, j, k) =
      replicate 60 '-' :
      "pure 0 = " <> show ((puresF ! i) 0 :: f Int) :
      toList (Vec.zipWith docLine joinArgsCache skolem2Cache)
      
      where
        join' :: f (f Int) -> f Int
        join' = joinsF ! j ! k

        docLine :: String -> f (f Int) -> String
        docLine s ffx = s ++ show (join' ffx)

main :: IO ()
main =
  do writeFile "monad-gen-F.txt" $ unlines $ monadGen @F Proxy
     writeFile "monad-gen-G.txt" $ unlines $ monadGen @G Proxy
     writeFile "monad-gen-H.txt" $ unlines $ monadGen @H Proxy
     writeFile "monad-gen-J.txt" $ unlines $ monadGen @J Proxy
     writeFile "monad-gen-W.txt" $ unlines $ monadGen @W Proxy
     writeFile "monad-gen-T.txt" $ unlines $ monadGen @T Proxy
