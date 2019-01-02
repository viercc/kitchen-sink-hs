module Main where

main :: IO ()
main = ppr $ buildBalanced [1..100 :: Int]

data Tree a = Node (Tree a) (Tree a) | Leaf a | Empty
   deriving (Show, Read, Eq, Ord)

ppr :: Show a => Tree a -> IO ()
ppr = putStrLn . prettyTree

prettyTree :: Show a => Tree a -> String
prettyTree = go 0
  where
    go indent t = case t of
      Empty -> "Empty"
      Leaf a -> show a
      Node t1 t2 -> "* " ++ go (indent+2) t1 ++ "\n" ++
                    replicate (indent+2) ' ' ++ go (indent+2) t2

buildBalanced :: [a] -> Tree a
buildBalanced = fromPart . toPart

{-

"Part" is a list of complete binary tree (2^d elements) with following
constraint:

* The first element is depth 0 tree (2^0 = 1 element), which is Leaf
* Depth of i-th element is i (full node) or i-1 (half node)

Example:

  # of elements  | List of depth | Is full?
  1              | [0]           | [1]
  2              | [0,0]         | [1,0]
  3              | [0,1]         | [1,1]
  4              | [0,0,1]       | [1,0,0]
  5              | [0,1,1]       | [1,1,0]
  6              | [0,0,2]       | [1,0,1]
  7              | [0,1,2]       | [1,1,1]
  8              | [0,0,1,2]     | [1,0,0,0]
  9              | [0,1,1,2]     | [1,1,0,0]
  10             | [0,0,2,2]     | [1,0,1,0]
  11             | [0,1,2,2]     | [1,1,1,0]
  12             | [0,0,1,3]     | [1,0,0,1]

-}
toPart :: [a] -> [(Bool, Tree a)]
toPart = foldr insertPart []

insertPart :: a -> [(Bool, Tree a)] -> [(Bool, Tree a)]
insertPart = incr0
  where
    incr0 a [] = [(True, Leaf a)]
    incr0 a ((_, t) : rest) = (True, Leaf a) : incr t rest
    
    incr t [] = [(False, t)]
    incr t ((d_i, t_i) : rest) =
      if d_i then (False, t) : incr t_i rest
             else (True, Node t t_i) : rest

fromPart :: [(Bool, Tree a)] -> Tree a
fromPart [] = Empty
fromPart ((_,t0) : rest) = foldl (\t (_,t') -> Node t t') t0 rest
