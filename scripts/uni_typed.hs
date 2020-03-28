#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}

import Data.Word
import Data.Functor.Identity

data Value' f = W32' (f Word32)
              | W64' (f Word64)
              | F32' (f Float)
              | F64' (f Double)

deriving instance (forall a. Show a => Show (f a)) => Show (Value' f)
deriving instance (forall a. Eq a => Eq (f a)) => Eq (Value' f)

type Value = Value' Identity

pattern W32 :: Word32 -> Value
pattern W32 x = W32' (Identity x)

pattern W64 :: Word64 -> Value
pattern W64 x = W64' (Identity x)

pattern F32 :: Float -> Value
pattern F32 x = F32' (Identity x)

pattern F64 :: Double -> Value
pattern F64 x = F64' (Identity x)

{-# COMPLETE W32, W64, F32, F64 #-}

data Pair x = Pair x x

combine :: Value -> Value -> Maybe (Value' Pair)
combine (W32 x) (W32 y) = Just $ W32' (Pair x y)
combine (W32 x) (W64 y) = Just $ W64' (Pair (fromIntegral x) y)
combine (W64 x) (W32 y) = Just $ W64' (Pair x (fromIntegral y))
combine (W64 x) (W64 y) = Just $ W64' (Pair x y)
combine (F32 x) (F32 y) = Just $ F32' (Pair x y)
combine (F32 x) (F64 y) = Just $ F64' (Pair (realToFrac x) y)
combine (F64 x) (F32 y) = Just $ F64' (Pair x (realToFrac y))
combine (F64 x) (F64 y) = Just $ F64' (Pair x y)
combine _       _       = Nothing

----------------------------------------------

data Op = Add | Sub | Mul | Div
    deriving (Show, Eq)

evalBinOp :: Op -> Value -> Value -> Maybe Value
evalBinOp Add x y = numOp (+) <$> combine x y
evalBinOp Sub x y = numOp (-) <$> combine x y
evalBinOp Mul x y = numOp (*) <$> combine x y
evalBinOp Div x y = divOp <$> combine x y

numOp :: (forall a. Num a => a -> a -> a) -> Value' Pair -> Value
numOp op (W32' (Pair x y)) = W32 (op x y)
numOp op (W64' (Pair x y)) = W64 (op x y)
numOp op (F32' (Pair x y)) = F32 (op x y)
numOp op (F64' (Pair x y)) = F64 (op x y)

divOp :: Value' Pair -> Value
divOp (W32' (Pair x y)) = W32 (x `div` y)
divOp (W64' (Pair x y)) = W64 (x `div` y)
divOp (F32' (Pair x y)) = F32 (x / y)
divOp (F64' (Pair x y)) = F64 (x / y)



main :: IO ()
main = do
  print
    [ evalBinOp Add (W32 5) (W32 6)
    , evalBinOp Div (W32 5) (W32 6)
    , evalBinOp Add (F32 1.5) (F32 3.6)
    , evalBinOp Div (F32 1.5) (F64 3.6)
    , evalBinOp Sub (F32 1.0) (W32 6)
    ]
