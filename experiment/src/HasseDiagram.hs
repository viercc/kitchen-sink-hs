module HasseDiagram where

import qualified Data.Map.Strict as Map

dotHasse :: (Ord x)
  => [x]             -- ^ All elements of the partial order
  -> (x -> String)   -- ^ Label of an element
  -> (x -> [x])      -- ^ Elements that covers x
  -> String          -- ^ Graph in DOT language
dotHasse vertices label covering = unlines doc
  where
    vs = zip [0 :: Int ..] vertices
    revIndex = Map.fromList [ (v,i) | (i,v) <- vs]

    nodeName i = "v" ++ show i
    indent = map ("  " ++)
    docNode (i,v) = nodeName i ++ " [label=\"" ++ label v ++ "\"]"
    docEdges (i,v) = "{" ++ unwords (nodeName <$> parentIds) ++ "} -> " ++ nodeName i
      where parentIds = [ j | w <- covering v, Just j <- [Map.lookup w revIndex] ]
    doc =
      [ "digraph {" ] ++
      indent [ "node [shape=box; color=white]" ] ++
      indent [ "edge [arrowhead=none]" ] ++
      indent (docNode <$> vs) ++
      indent (docEdges <$> vs) ++
      [ "}" ]
