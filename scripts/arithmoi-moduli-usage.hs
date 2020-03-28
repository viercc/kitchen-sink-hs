#!/usr/bin/env cabal
{- cabal:
build-depends: base, random, arithmoi
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Data.Proxy
import GHC.TypeLits(someNatVal, SomeNat(..))

import System.Random (Random(..))

import Math.NumberTheory.Moduli
import Math.NumberTheory.Moduli.Singleton

import Data.Functor

main :: IO ()
main =
  do m <- randomRIO (2, 14 :: Integer)
     case someNatVal m of
       Nothing -> putStrLn $ "Failed! " ++ show m
       Just mNat ->
         do print (f mNat)
            case mNat of
              SomeNat mName ->
                do print (g mName)
                   mapM_ (\n -> print $ process n mName) [0..10]

process :: (KnownNat m) => Integer -> Proxy m -> (Mod m, [Mod m])
process x mName =
  let x' = fromInteger x
  in (x', sqrtsMod sfactors x')

createMod :: (KnownNat m) => Integer -> Proxy m -> Mod m
createMod i _ = fromInteger i

f :: SomeNat -> Integer
f (SomeNat mName) = getVal finalAnswer
  where
    x = reallyComplexCalculation (createMod 100 mName) 200
    y = reallyHeavyMath x 300 400
    finalAnswer = x + y

reallyComplexCalculation :: (KnownNat m) => Mod m -> Mod m -> Mod m
reallyComplexCalculation = (+)
reallyHeavyMath :: (KnownNat m) => Mod m -> Mod m -> Integer -> Mod m
reallyHeavyMath x y _ = x * y

withKnownNat :: forall r . SomeNat -> (forall m . KnownNat m => Proxy m -> r) -> r
withKnownNat (SomeNat mName) cont = cont mName
    
g :: forall m . KnownNat m => Proxy m -> Integer
g _ = getVal $ 100 + 200 + fromInteger @(Mod m) 300
    -- You can use TypeApplications here
