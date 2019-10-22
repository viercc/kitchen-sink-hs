{-|

Logging Monad inspired by: <http://hackage.haskell.org/package/co-log>

-}
{-# LANGUAGE DeriveFunctor #-}
module Monad.Logger where

import Control.Monad.Trans
import Data.Functor.Contravariant

newtype LogHandler m msg = LogHandler { getLogHandler :: msg -> m () }

instance Contravariant (LogHandler m) where
  contramap f (LogHandler act) = LogHandler $ act . f

newtype LoggerT msg m a =
  LoggerT {
    runLoggerT :: LogHandler m msg -> m a
  }
  deriving (Functor)

instance (Applicative m) => Applicative (LoggerT msg m) where
  pure a = LoggerT $ const (pure a)
  LoggerT mf <*> LoggerT ma = LoggerT $ \h -> mf h <*> ma h

instance (Monad m) => Monad (LoggerT msg m) where
  return = pure
  LoggerT ma >>= k = LoggerT $ \h -> ma h >>= \a -> runLoggerT (k a) h

instance MonadTrans (LoggerT msg) where
  lift ma = LoggerT $ const ma

instance MonadIO m => MonadIO (LoggerT msg m) where
  liftIO = lift . liftIO

putLog :: msg -> LoggerT msg m ()
putLog msg = LoggerT $ \handler -> getLogHandler handler msg

mapMsg :: (msg -> msg') -> LoggerT msg m a -> LoggerT msg' m a
mapMsg f (LoggerT ma) = LoggerT $ \handler -> ma (contramap f handler)

bindMsg :: (msg -> LoggerT msg' m ()) -> LoggerT msg m a -> LoggerT msg' m a
bindMsg f (LoggerT ma) =
  LoggerT $ \handler ->
    let handler' = LogHandler $ \msg ->
          runLoggerT (f msg) handler
    in ma handler'

-------------------------------

stdoutHandler :: LogHandler IO String
stdoutHandler = LogHandler putStrLn

stdoutHandler' :: LogHandler IO String
stdoutHandler' = contramap ("[LOG]"++) stdoutHandler

testIntLogger :: (Monad m) => LoggerT Int m ()
testIntLogger = do
  putLog 1
  putLog 2
  putLog 3

testBoolLogger :: (Monad m) => LoggerT Bool m ()
testBoolLogger = do
  putLog True
  putLog False

data LogEntry = IntLog Int | BoolLog Bool
  deriving (Show)

testLogEntryLogger :: (MonadIO m) => LoggerT LogEntry m ()
testLogEntryLogger = do
  mapMsg IntLog  testIntLogger
  liftIO $ putStrLn "Running arbitrary IO Action!!"
  mapMsg BoolLog testBoolLogger

testLogger :: (MonadIO m) => LoggerT String m ()
testLogger = do
  putLog "logging begins"
  mapMsg show testLogEntryLogger
  putLog "logging ends"

main :: IO ()
main = runLoggerT testLogger stdoutHandler'

