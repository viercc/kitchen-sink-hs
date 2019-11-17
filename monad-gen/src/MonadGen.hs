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

import           Vec
import           Enum1
import           Enum1.Extra
import           Targets
import           Util

------------------------
-- Tests

checkLeftUnit :: (Traversable m, Enum1 m, Eq (m b)) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m b -> Bool
checkLeftUnit pure' join' mb = join' (pure' mb) == mb

checkRightUnit :: (Traversable m, Enum1 m, Eq (m b)) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m b -> Bool
checkRightUnit pure' join' mb = join' (fmap pure' mb) == mb

checkActionAssoc :: (Functor m, Enum1 m, Eq (m ())) =>
  (forall a. m (m a) -> m a) ->
  m () -> m () -> m () -> Bool
checkActionAssoc join' m1 m2 m3 =
  (m1 `op` m2) `op` m3 == m1 `op` (m2 `op` m3)
  where
    op x y = join' (y <$ x)

checkAssoc :: (Traversable m, Enum1 m, Eq (m b)) =>
  (forall a. m (m a) -> m a) -> m (m (m b)) -> Bool
checkAssoc join' mmmb = join' (join' mmmb) == join' (fmap join' mmmb)

counterExamplesAssoc :: (Traversable m, Enum1 m, Eq (m Int)) =>
  (forall a. m (m a) -> m a) -> [m (m (m Int))]
counterExamplesAssoc join' =
  [ mmma | mmma <- toList skolem3, join' (join' mmma) /= join' (fmap join' mmma)]

forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
forAll = flip all

cache :: Vec a -> Vec a
cache = fromVector . toVector

monadGen
  :: forall f.
       (forall a. Eq a => Eq (f a),
       forall a. Show a => Show (f a),
       Traversable f,
       Enum1 f,
       CoEnum1 f)
       => Proxy f -> [String]
monadGen _ = header ++ (okayPairs >>= docResult)
  where
    puresF :: forall a. Vec (a -> f a)
    puresF = allPures
    
    joinsF :: Vec (Vec (f (f a) -> f a))
    joinsF = fmap (. Comp1) . runTemplate <$> enumTemplates @(f :.: f) @f

    actions :: Vec (f ())
    actions = cache $ enum1 (singleton ())
    
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
         guard $ forAll actions $ checkLeftUnit pure' join0
         guard $ forAll actions $ checkRightUnit pure' join0
         guard $ forAll actions $ \m1 ->
           forAll actions $ \m2 ->
             forAll actions $ \m3 ->
               checkActionAssoc join0 m1 m2 m3
         k <- [0 .. n - 1]
         let join' :: forall b. f (f b) -> f b
             join' = (joinsF ! j) ! k
         guard $ forAll skolemCache $ checkLeftUnit pure' join'
         guard $ forAll skolemCache $ checkRightUnit pure' join'
         guard $ forAll skolem3Cache $ checkAssoc join'
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
  do writeFile' "monad-gen-F.txt" $ monadGen @F Proxy
     writeFile' "monad-gen-G.txt" $ monadGen @G Proxy
     writeFile' "monad-gen-H.txt" $ monadGen @H Proxy
     writeFile' "monad-gen-W.txt" $ monadGen @W Proxy
     -- writeFile' "monad-gen-T.txt" $ monadGen @T Proxy
     -- writeFile' "monad-gen-J.txt" $ monadGen @J Proxy
