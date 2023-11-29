{-# LANGUAGE DeriveFunctor #-}
module Main where

import Hefty
import Control.Monad.Trans.Free (FreeT)

main :: IO ()
main = runEffs main'

data Console a = PutStr String a | GetLine (String -> a)
    deriving Functor

main' :: Effs IO ()
main' = do
    withHandler consoleHandler main''
    withHandler fakeInputConsoleHandler main''

main'' :: FreeT Console (Effs IO) ()
main'' = do
    inl (PutStr "Hello\n" ())
    userInput <- inl (GetLine id)
    inl (PutStr ("You said " ++ show userInput ++ "\n\n") ())

consoleHandler :: Console x -> Effs IO (Either x ())
consoleHandler (PutStr str x) = lift' (putStr str) >> pure (Left x)
consoleHandler (GetLine k) = lift' getLine >>= \str -> pure (Left (k str))

fakeInputConsoleHandler :: Console x -> Effs IO (Either x ())
fakeInputConsoleHandler (PutStr str x) = consoleHandler (PutStr str x)
fakeInputConsoleHandler (GetLine k) = pure (Left (k "stub"))