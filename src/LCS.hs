module LCS(
  emptyTrie, insertTrie, fromList,
  union, intersection,
  substrings,
  
  maximalSequencesWithLength,

  longestCommonSubstring,
  showTree) where

import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)

import Data.List (foldl', foldl1', maximum)
import Data.Maybe (fromMaybe)

-- | Prefix tree
newtype Trie a = Trie (Map a (Trie a))
  deriving (Eq)

instance Show a => Show (Trie a) where
  showsPrec p t =
    showParen (p > 10) $ ("fromList "++) . shows (maximalSequences t)

emptyTrie :: Trie a
emptyTrie = Trie Map.empty

insertTrie :: (Ord a) => [a] -> Trie a -> Trie a
insertTrie [] t = t
insertTrie (a:as) (Trie node) =
  let tree' = fromMaybe emptyTrie $ Map.lookup a node
  in Trie $ Map.insert a (insertTrie as tree') node

fromList :: (Ord a) => [[a]] -> Trie a
fromList = foldl' (flip insertTrie) emptyTrie

substrings :: (Ord a) => [a] -> Trie a
substrings as = foldl' union emptyTrie $ scanr step emptyTrie as
  where
    step a t = Trie (Map.singleton a t)

union :: (Ord a) => Trie a -> Trie a -> Trie a
union (Trie node1) (Trie node2) =
  Trie $ Map.unionWith union node1 node2

intersection :: (Ord a) => Trie a -> Trie a -> Trie a
intersection (Trie node1) (Trie node2) =
  Trie (Map.intersectionWith intersection node1 node2)

maximalSequencesWithLength :: Trie a -> [(Int, [a])]
maximalSequencesWithLength = go 0
  where go n (Trie node) = n `seq`
          case Map.toList node of
            [] -> [(n, [])]
            edges -> [ (len, a:as) | (a,t) <- edges, (len, as) <- go (n+1) t ]

maximalSequences :: Trie a -> [[a]]
maximalSequences = map snd . maximalSequencesWithLength

longestCommonSubstring :: (Ord a) => [[a]] -> [a]
longestCommonSubstring [] = []
longestCommonSubstring ts = snd . maximum $ maximalSequencesWithLength lcs
  where
    lcs = foldl1' intersection (map substrings ts)

showTree :: (Show a) => Trie a -> String
showTree = unlines . go 0
  where
    go depth (Trie node) =
      Map.toList node >>= \(a,t) ->
         (replicate depth ' ' ++ show a) : go (depth+2) t
