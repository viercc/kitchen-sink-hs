{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE MagicHash            #-}
module CheapRecord(
  Ex(..), ExField(..), normalize, mkEx,
  sample1, sample2, sample3, sample4
) where

import Data.Ord
import GHC.Base (getTag, Int(..))

import qualified Data.List.Ordered as OL

{-
Based on the question asked by u/King_of_the_Homeless

https://www.reddit.com/r/haskell/comments/93gbdn/monthly_hask_anything_august_2018/e4wv5ol/
-}

data Ex = Ex {
    exFoo :: Int
  , exBar :: Bool
  , exBaz :: (Float, Float)
  , exBaq :: [String]
  }
  deriving (Show)

data ExField
    = ExFoo Int
    | ExBar Bool
    | ExBaz (Float, Float)
    | ExBaq [String]
    deriving (Show)

normalize :: [ExField] -> [ExField]
normalize = nubLastSortBy (comparing tag)
  where tag ef = I# (getTag ef)

mkEx :: [ExField] -> Maybe Ex
mkEx efs = case normalize efs of
  [ ExFoo exFoo,
    ExBar exBar,
    ExBaz exBaz,
    ExBaq exBaq ] -> Just Ex{..}
  _ -> Nothing


sample1, sample2, sample3, sample4 :: [ExField]
sample1 = [ExFoo 1, ExBar True, ExBaz (1,2), ExBaq []]
sample2 = [ExFoo 1, ExBar True, ExBaz (1,2)]
sample3 = reverse sample1
sample4 = [ExBar True, ExBar False, ExBaz (1,2)] ++
          replicate 10000 (ExBaq []) ++
          map ExFoo [1..400000]

-- | nubSortBy but keeps last element among equivalent values
nubLastSortBy :: (a -> a -> Ordering) -> [a] -> [a]
nubLastSortBy cmp = go . map (:[])
  where
    go []          = []
    go [as]        = as
    go (as:bs:css) = go $ OL.unionBy cmp bs as : pairs css
    --                    ^^^^^^^^^^^^^^^^^^^^
    --                    argurments are flipped
    
    pairs []   = []
    pairs [as] = [as]
    pairs (as:bs:css) = OL.unionBy cmp bs as : pairs css
    --                  ^^^^^^^^^^^^^^^^^^^^
