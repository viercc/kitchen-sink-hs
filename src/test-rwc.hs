{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ApplicativeDo #-}
module Main where

import Data.IORef

data User = User { userId :: Int
                 , userName :: String
                 , userHasCar :: Bool
                 }
            deriving (Show)

mkUserA :: (Applicative f) => f Int -> f String -> f Bool -> f User
mkUserA mkFreshId getName getHasCar =
  do userName <- getName
     userHasCar <- getHasCar
     userId <- mkFreshId
     return User{..}

mkUserM :: (Monad m) => m Int -> m String ->  m Bool -> m (Maybe User)
mkUserM mkFreshId getName getHasCar =
  do userHasCar <- getHasCar
     userName <- getName
     if userHasCar
       then do userId <- mkFreshId
               return $ Just User{..}
       else return Nothing

main :: IO ()
main =
  do refUserNum <- newIORef 0
     let mkFreshId = do n <- readIORef refUserNum
                        modifyIORef' refUserNum succ 
                        return n
         getName = putStr "Your Name:" >> getLine
         getHasCar = putStr "You have a car (True/False):" >> readLn
     mkUserA mkFreshId getName getHasCar >>= print
     mkUserM mkFreshId getName getHasCar >>= print
     
