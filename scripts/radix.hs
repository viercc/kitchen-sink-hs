import Control.Monad (guard)
import Data.Char (intToDigit)
import Data.List (isInfixOf, foldl')
import Data.Maybe (mapMaybe)

radix :: Integral a => a -> a -> [a]
radix b = reverse . go
  where
    go 0 = []
    go x = let (x',a) = x `divMod` b in a : go x'

unradix :: Integral a => a -> [a] -> a
unradix b = foldl' step 0
  where
    step acc a = acc * b + a

zeropad :: Num a => Int -> [a] -> [a]
zeropad ncols as = replicate (ncols - length as) 0 ++ as

main :: IO ()
main = mapM_ print $ take 100 $ recNumbers

recNumbersAt :: Int -> [(Int, Int)]
recNumbersAt b =
  do x <- [b..]
     let dec = radix b x
         y = unradix 10 dec
     guard $ dec `isInfixOf` radix b y
     return (y, b)

recNumbers :: [(Int, Int, String)]
recNumbers =
  do x <- [9..]
     let dec = radix 9 x
         y = unradix 10 dec
         minBase = maximum dec + 1
     b <- [minBase .. 9]
     let lowerBase = radix b y
     guard $ dec `isInfixOf` lowerBase
     return (y,b, intToDigit <$> lowerBase)

mergeOn :: Ord b => (a -> b) -> [[a]] -> [a]
mergeOn f = go
  where
    go [] = []
    go (as:ass) = as `mer` go (pairs ass)
    
    pairs [] = []
    pairs [as] = [as]
    pairs (as:as':ass) = mer as as' : pairs ass

    mer (x:xs) (y:ys)
      | f x <= f y  = x : mer xs (y:ys)
      | otherwise   = y : mer (x:xs) ys
    mer [] ys = ys
    mer xs [] = xs