{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import Debug.Trace
import Control.Arrow ((***), (&&&), first, second)

main :: IO ()
main = print (para combinedAlg five)
  where
    five = S (S (S (S (S Z))))

-------------------------

type family Base (t :: *) :: * -> *

class (Functor (Base t)) => Recursive t where
  unwrap :: t -> Base t t
  cata :: (Base t a -> a) -> t -> a
  cata f = let go = f . fmap go . unwrap in go 
  para :: (Base t (t, a) -> a) -> t -> a
  para f = let go = f . fmap (id &&& go) . unwrap in go

data Nat = Z | S Nat
   deriving (Show, Eq)

type instance Base Nat = Maybe

instance Recursive Nat where
  unwrap Z = Nothing
  unwrap (S n) = Just n

-----------------------------

type ParaF t a = Base t (t, a)
type ParaAlg t a = ParaF t a -> a

funzipPara :: Functor (Base t) => ParaF t (a,b) -> (ParaF t a, ParaF t b)  
funzipPara = fmap (fst &&& fst.snd ) &&& fmap (fst &&& snd.snd)  

combineParaAlg :: (Functor (Base t)) =>  
  ParaAlg t a -> -- The first t-algebra  
  ParaAlg t b -> -- The second t-algebra  
  ParaAlg t (a,b) -- The combined t-algebra  
combineParaAlg f g = (f *** g) . funzipPara

predAlg :: ParaAlg Nat Nat
predAlg Nothing      = Z
predAlg (Just (n,_)) = n

toIntAlg :: ParaAlg Nat Int
toIntAlg Nothing      = 0
toIntAlg (Just (_,i)) = i + 1

-- Will compiling with -O2 optimize away fmap @Maybe by deforestation?
combinedAlg :: ParaAlg Nat (Nat, Int)
combinedAlg = combineParaAlg predAlg toIntAlg

------------------------------

data MyExpr a = AExpr a
              | BExpr (MyExpr a) (MyExpr a) 
              deriving (Show, Eq, Functor)

data MyExprF a r = AExprF a | BExprF r r
    deriving (Show, Eq, Functor)

type instance Base (MyExpr a) = MyExprF a

instance Recursive (MyExpr a) where
  unwrap (AExpr x)   = AExprF x
  unwrap (BExpr a b) = BExprF a b

af = AExpr
bf = BExpr

myTracer :: String -> (MyExprF Int (MyExpr Int, Int) -> Int)
myTracer s tree = 
    case tree of
        BExprF a b -> traceShow (s ++ show (snd a + snd b)) (snd a + snd b)
        AExprF x   -> traceShow (s ++ "1") 1

myTracers :: MyExprF Int (MyExpr Int, (Int,Int)) -> (Int,Int)
myTracers = algebra1  `combineParaAlg'` algebra2
    where
        algebra1 = myTracer "First pass:"
        algebra2 = myTracer "Second pass:"

someFunc2 :: IO ()
someFunc2 = print result
    where 
      tree = bf (af 0) (af 1)
      result = para algebra tree
      algebra = myTracers

combineParaAlg' :: (Functor (Base t)) =>  
  ParaAlg t a -> -- The first t-algebra  
  ParaAlg t b -> -- The second t-algebra  
  ParaAlg t (a,b) -- The combined t-algebra  
combineParaAlg' f g tab =
  let a = f $ fmap (second fst) tab
      b = g $ fmap (second snd) tab
  in a `seq` b `seq` (a,b)

someFunc3 :: IO ()
someFunc3 = print result
  where
    step a (x,y) = (trace ("A" ++ show a) (x + a),
                    trace ("B" ++ show a) (y + a))
    result = foldr step (0,0) [1,2,3,4::Int]

someFunc4 :: IO ()
someFunc4 = print result
  where
    step' a (!x,!y) = (trace ("A" ++ show a) (x + a),
                       trace ("B" ++ show a) (y + a))
    result = foldr step' (0,0) [1,2,3,4::Int]
