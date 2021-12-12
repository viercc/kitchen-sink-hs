module TestFreeAp where

import Control.Monad.Writer

import Control.Monad.Free.Ap

foo :: Free IO ()
foo = do liftF (putStrLn "foo1")
         liftF (putStrLn "foo2")

bar :: Free IO ()
bar = do liftF (putStrLn "bar1")
         liftF (putStrLn "bar2")

main :: IO ()
main = 
  do putStrLn "--------"
     retract (fmap const foo <*> bar)
     putStrLn "--------"
     retract (fmap const foo `ap` bar)
