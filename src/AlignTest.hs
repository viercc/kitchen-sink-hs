{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import Control.Applicative

import Data.Bifunctor
import Data.Monoid (Sum)

import Control.Monad.Reader
import Data.Functor.Compose

import Data.These
import Data.Align

import qualified Data.Map as Map

import Test.QuickCheck

instance (Monoid k) => Align (Const k) where
  nil = Const mempty
  align (Const k1) (Const k2) = Const (k1 `mappend` k2)

instance (Align f) => Align (ReaderT e f) where
  nil = ReaderT $ pure nil
  align (ReaderT f1) (ReaderT f2) = ReaderT $ liftA2 align f1 f2

instance (Align f, Align g) => Align (Compose f g) where
  nil = Compose nil
  align (Compose fga) (Compose fgb) = Compose $ alignWith u fga fgb
    where u (This ga) = This <$> ga
          u (That gb) = That <$> gb
          u (These ga gb) = align ga gb

swap :: These a b -> These b a
swap (This a) = That a
swap (That b) = This b
swap (These a b) = These b a

assoc1 :: These a (These b c) -> These (These a b) c
assoc1 a_bc = case a_bc of
  This a -> This (This a)
  That bc -> case bc of
    This b -> This (That b)
    That c -> That c
    These b c -> These (That b) c
  These a bc -> case bc of
    This b -> This (These a b)
    That c -> These (This a) c
    These b c -> These (These a b) c

assoc2 :: These (These a b) c -> These a (These b c)
assoc2 = swap . first swap . assoc1 . swap . first swap

badAlign1 :: [a] -> [b] -> [These a b]
badAlign1 as bs = fmap This as ++ fmap That bs

badAlign2 :: [a] -> [b] -> [These a b]
badAlign2 = zipWith These

badAlign3 :: [a] -> [b] -> [These a b]
badAlign3 as [] = This <$> as
badAlign3 [] bs = That <$> bs
badAlign3 as bs = zipWith These as bs

badAlign3Map :: Map.Map Int a -> Map.Map Int b -> Map.Map Int (These a b)
badAlign3Map as bs
   | Map.null bs = This <$> as
   | Map.null as = That <$> bs
   | otherwise   = Map.intersectionWith These as bs

propIdempotence
  :: forall f. (Functor f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => (forall a b. f a -> f b -> f (These a b)) -> f Bool -> Property
propIdempotence al xs = al xs xs === fmap (\x -> These x x) xs

propCommutative
  :: forall f. (Functor f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => (forall a b. f a -> f b -> f (These a b)) -> f Bool -> f Int -> Property
propCommutative al xs ys = al xs ys === fmap swap (al ys xs)

propAssociative
  :: forall f. (Functor f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => (forall a b. f a -> f b -> f (These a b)) -> f Bool -> f Int -> f Char -> Property
propAssociative al xs ys zs =
  fmap assoc1 (al xs (al ys zs)) === al (al xs ys) zs

propLeftUnit
  :: forall f. (Functor f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => f () -> (forall a b. f a -> f b -> f (These a b)) -> f Bool -> Property
propLeftUnit z al xs =
  al z xs === fmap That xs

propRightUnit
  :: forall f. (Functor f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => f () -> (forall a b. f a -> f b -> f (These a b)) -> f Bool -> Property
propRightUnit z al xs =
  al xs z === fmap This xs

checkAll
  :: forall f. (Functor f
               , forall a. Show a => Show (f a)
               , forall a. Eq a => Eq (f a)
               , forall a. Arbitrary a => Arbitrary (f a))
  => f () -> (forall a b. f a -> f b -> f (These a b)) -> IO ()
checkAll z al =
  do putStr "<Idempotence> "
     quickCheck $ propIdempotence al
     putStr "<Commutative> "
     quickCheck $ propCommutative al
     putStr "<Associative> "
     quickCheck $ propAssociative al
     putStr "<LeftUnit>    "
     quickCheck $ propLeftUnit z al
     putStr "<RightUnit>   "
     quickCheck $ propRightUnit z al

main :: IO ()
main =
  do putStrLn "Const (Sum Int)"
     checkAll @(Const (Sum Int)) (Const 0) align
     
     putStrLn "Const [Int]"
     checkAll @(Const [Int]) (Const []) align
     
     putStrLn "[]"
     checkAll [] align

     putStrLn "badAlign1"
     checkAll [] badAlign1
     
     putStrLn "badAlign2"
     checkAll [] badAlign2
     
     putStrLn "badAlign3"
     checkAll [] badAlign3
     
     putStrLn "badAlign3Map"
     checkAll Map.empty badAlign3Map
