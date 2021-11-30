{-

The idea directly taken from

https://www.reddit.com/r/haskell/comments/ahu6jp/fun_fact_the_continuation_monad_cont_r_a_has_an/

-}
module ContEq2 where

import Data.Foldable
import qualified Data.Map as Map
import Numeric.Natural

newtype Cont r a = Cont { runCont :: (a -> r) -> r }

class Searchable a where
  -- | Takes a predicate @p@. If there is at least one value of type @a@
  --   which satisfies @p@, return that value. Otherwise,
  --   return any value of type @a@.
  epsilon :: (a -> Bool) -> a

instance Searchable Bool where
  epsilon p = p True
  -- epsilon p = if p True then True else False

instance Searchable () where
  epsilon _ = ()

instance Searchable a => Searchable [a] where
  epsilon p =
    if p [] then []
            else let a0 = epsilon $ \a -> p (a : epsilon (p . (a:)))
                 in a0 : epsilon (p . (a0:))

instance (Ord a, Searchable r) => Searchable (a -> r) where
  epsilon p = go Map.empty
    where go guess a = case Map.lookup a guess of
            Just r -> r
            Nothing ->
              epsilon $ \r ->
                let f b | b < a     = go guess b
                        | otherwise = go (Map.insert a r guess) b
                in p f

instance (Ord a, Searchable r, Eq r) => Eq (Cont r a) where
  (Cont arr) == (Cont arr') = pointEq $ epsilon (not . pointEq)
    where
      pointEq ar = arr ar == arr' ar

-----------------------------------

class Eq a => POrd a where
  (<=?) :: a -> a -> Bool

pcmp :: POrd a => a -> a -> Maybe Ordering
pcmp x y = case (x <=? y, y <=? x) of
  (True, True) -> Just EQ
  (True, False) -> Just LT
  (False, True) -> Just GT
  (False, False) -> Nothing

instance POrd Bool where
  (<=?) = (<=)

instance (Ord a, Searchable r, POrd r) => POrd (Cont r a) where
  (Cont arr) <=? (Cont arr') = pointLeq $ epsilon (not . pointLeq)
    where
      pointLeq ar = arr ar <=? arr' ar

-- Total ordering

cmpContNat :: Cont Bool Natural -> Cont Bool Natural -> Ordering
cmpContNat x y = case pcmp x y of
  Just result -> result
  Nothing -> cmpContNat (mask False x) (mask False y)
              <> cmpContNat (mask True x) (mask True y)
  where
    mask :: Bool -> Cont Bool Natural -> Cont Bool Natural
    mask b (Cont c) = Cont $ \k -> c (\i -> if i == 0 then b else k (i - 1))

-- test

ex1, ex2, ex3, ex4, ex5 :: Cont Bool Natural
ex1 = Cont $ \k -> (k 0 || k 2) && (k 1 || k 2)
ex2 = Cont $ \k -> (k 0 && k 1) || k 2
ex3 = Cont $ \k -> (k 0 && not (k 1)) || k 2
ex4 = Cont $ \k -> k 0 && (k 1 || k 2)
ex5 = Cont $ \k -> k 0 && k 1
ex6 = Cont $ \k -> k 0 && k 2

exes :: [Cont Bool Natural]
exes = [ex1, ex2, ex3, ex4, ex5, ex6]

-- ex1 == ex2   ex3
--      \       /
--      ex4    /
--     /  \   /
--   ex5   ex6

main :: IO ()
main =
  do putStrLn "Table[==]"
     forM_ exes $ \x ->
       do forM_ exes $ \y ->
            putStr $ if x == y then " 1" else " 0"
          putStr "\n"
     putStrLn "Table[<=?]"
     forM_ exes $ \x ->
       do forM_ exes $ \y ->
            putStr $ if x <=? y then " 1" else " 0"
          putStr "\n"
     putStrLn "Table[cmp]"
     forM_ exes $ \x ->
       do forM_ exes $ \y ->
            putStr . show $ cmpContNat x y
          putStr "\n"
