{-# LANGUAGE CPP #-}
-- https://www.reddit.com/r/haskell/comments/zvbodl/noobie_help_with_infinitelazy_list_unexpected/
module Main(main) where

zip_iterate ::  [[a] -> [a]] -> [a] -> [[a]]
zip_iterate functions initial_value = zip_iterate_aux functions initial_value 0
    where
        zip_iterate_aux :: [[a] -> [a]] -> [a] -> Int -> [[a]]
        zip_iterate_aux func_list input count =
            input : (zip_iterate_aux func_list ((func_list !! count)input) (count + 1))

makeWeights :: Integer -> [Float]
makeWeights n = fromInteger <$> [1 .. n]

trainStep :: [Float] -> [Float]
trainStep xs =
    let norm = sqrt $ sum [x * x | x <- xs]
     in [x / norm | x <- xs]

makeTrainFunctions :: dummyArg -> [[Float] -> [Float]]
makeTrainFunctions _ = repeat trainStep
{-# NOINLINE makeTrainFunctions #-}

main = do
    let weights :: [Float]
        weights = makeWeights 3

        train_functions = makeTrainFunctions "dummy"

        -- iterCount = 300000
        iterCount = 300000
    let final_weight = (zip_iterate train_functions weights) !! iterCount
    print final_weight

#ifdef WITH_NEXT
    let final_next = (zip_iterate (drop iterCount train_functions) final_weight) !! (1)
    print final_next
#endif

    -- return final_weight
