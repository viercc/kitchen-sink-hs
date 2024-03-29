module OrM where

orM :: (Monad m) => m Bool -> m Bool -> m Bool
orM mx my = do x <- mx; if x then return True else my

andM :: (Monad m) => m Bool -> m Bool -> m Bool
andM mx my = do x <- mx; if x then my else return False

allValues :: [Maybe Bool]
allValues = [Just False, Just True, Nothing]

allResults :: [(Maybe Bool, Maybe Bool, Maybe Bool)]
allResults = [ (x, y, orM x y) | x <- allValues, y <- allValues ]
