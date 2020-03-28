{-

The idea directly taken from

https://www.reddit.com/r/haskell/comments/ahu6jp/fun_fact_the_continuation_monad_cont_r_a_has_an/

-}
module ContEq2 where

import Data.Foldable
import qualified Data.Map as Map

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

instance POrd Bool where
  (<=?) = (<=)

instance (Ord a, Searchable r, POrd r) => POrd (Cont r a) where
  (Cont arr) <=? (Cont arr') = pointLeq $ epsilon (not . pointLeq)
    where
      pointLeq ar = arr ar <=? arr' ar

ex1, ex2, ex3, ex4, ex5 :: Cont Bool Integer
ex1 = Cont $ \ib -> (ib 7 && ib 4) || ib 8
ex2 = Cont $ \ib -> (ib 7 || ib 8) && (ib 4 || ib 8)
ex3 = Cont $ \ib -> (ib 7 || ib 8) && ib 4
ex4 = Cont $ \ib -> ib 7 && ib 4
ex5 = Cont $ \ib -> ib 5

exes :: [Cont Bool Integer]
exes = [ex1, ex2, ex3, ex4, ex5]

-- ex4 <=? ex3 <=? ex2 == ex1
-- ex5 has no relation to ex1,ex2,ex3,ex4

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
