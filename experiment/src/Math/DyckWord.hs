{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Math.DyckWord where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Equivalence.Monad

import Control.Applicative
import Data.Foldable (for_)
import Data.Char (isSpace)

-- | Rooted ordered tree
newtype Tree = T [Tree]
  deriving (Eq, Ord, Show)

-- | Number of nodes
size :: Tree -> Int
size (T xs) = 1 + sum (size <$> xs)

-- | Children in order
children :: Tree -> [Tree]
children (T xs) = xs

-- | Root-only tree
leaf :: Tree
leaf = T []

-- | Prepend a child
cons :: Tree -> Tree -> Tree
cons x (T xs) = T (x : xs)

-- | Rotation of a tree
rotate :: Tree -> Tree
rotate (T []) = T []
rotate (T (x : xs)) = T $ children x ++ [T xs]

-- | generates all @Tree@ of size @n@
--
-- >>> map prettyDyck $ generateTrees 1
-- [""]
-- 
-- >>> map prettyDyck $ generateTrees 2
-- ["[]"]
--
-- >>> map prettyDyck $ generateTrees 3
-- ["[][]","[[]]"]
-- 
-- >>> map prettyDyck $ generateTrees 4
-- ["[][][]","[][[]]","[[]][]","[[][]]","[[[]]]"]
generateTrees :: Int -> [Tree]
generateTrees n
  | n < 1 = []
  | n == 1 = [ leaf ]
  | otherwise = do
      j <- [1 .. n - 1]
      let k = n - j
      t <- generateTrees j
      u <- generateTrees k
      pure $ cons t u

-- | Classify all trees of given size @n@ to orbits of 'rotate'
--
-- >>> map (map prettyDyck) $ treeClasses 3
-- [["[][]","[[]]"]]
-- >>> map (map prettyDyck) $ treeClasses 4
-- [["[][][]","[[][]]"],["[][[]]","[[]][]","[[[]]]"]]
-- >>> length . treeClasses <$> [3..9]
-- [1,2,3,6,14,34,95]
-- 
treeClasses :: Int -> [[Tree]]
treeClasses n = map Set.toList $ classifyByAction rotate (generateTrees n) 

-- | Alphabets
data S = L | R
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | Is [S] a Dyck word? (balanced Ls and Rs?)
--
-- >>> isDyck []
-- True
-- >>> isDyck [L,L,R,L,R,R,L,R]
-- True
-- >>> isDyck [L,L,R,L]
-- False
-- >>> isDyck [L,R,R,L]
-- False
isDyck :: [S] -> Bool
isDyck = go 0
  where
    go :: Int -> [S] -> Bool
    go n [] = n == 0
    go n (L : xs') = go (n + 1) xs'
    go n (R : xs') = n > 0 && go (n - 1) xs'

-- | Parse a Dyck word
--
-- >>> parseDyck []
-- Just (T [])
-- >>> parseDyck [L,L,R,L,R,R,L,R]
-- Just (T [T [T [],T []],T []])
-- >>> parseDyck [L,L,R,L]
-- Nothing
-- >>> parseDyck [L,R,R,L]
-- Nothing
parseDyck :: [S] -> Maybe Tree
parseDyck xs = snd <$> runParser (p <* eof) xs
  where
    p = (cons <$ char L <*> p <* char R <*> p) <|> pure leaf

toDyck :: Tree -> [S]
toDyck = ($ []) . go
  where
    go (T []) = id
    go (T (x : xs)) = (L :) . go x . (R :) . go (T xs)

prettyDyck :: Tree -> String
prettyDyck = map tr . toDyck
  where
    tr L = '['
    tr R = ']'

parsePrettyDyck :: String -> Maybe Tree
parsePrettyDyck xs = traverse tr xs >>= parseDyck . concat
  where
    tr '[' = Just [L]
    tr ']' = Just [R]
    tr c | isSpace c = Just []
         | otherwise = Nothing

----

newtype Parser c a = Parser { runParser :: [c] -> Maybe ([c], a) }
  deriving Functor

instance Applicative (Parser c) where
  pure a = Parser $ \str -> Just (str, a)
  px <*> py = Parser $ \s0 ->
    do (s1,x) <- runParser px s0
       (s2,y) <- runParser py s1
       pure (s2, x y)

instance Alternative (Parser c) where
  empty = Parser $ const Nothing
  pa <|> pb = Parser $ \s0 -> runParser pa s0 <|> runParser pb s0

eof :: Parser c ()
eof = Parser $ \str -> case str of
  [] -> Just ([], ())
  _ -> Nothing

char :: Eq c => c -> Parser c ()
char c = Parser $ \str -> case str of
  c' : rest | c == c' -> Just (rest, ())
  _ -> Nothing

----

classifyByAction :: forall x. (Ord x) => (x -> x) -> [x] -> [Set.Set x]
classifyByAction f xs = runEquivM Set.singleton Set.union body
  where
    body :: forall s. EquivM s (Set.Set x) x [Set.Set x]
    body = do
      for_ xs $ \x -> equate x (f x)
      cs <- classes
      mapM desc cs
