-- https://discourse.haskell.org/t/question-about-mkweakptr-and-derefweak/11509/3

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- to show deRefWeak's Noting result.

module Lib2 (someFunc) where

import Control.Concurrent
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Logger
import Control.Monad.Reader
import qualified Data.Text as DT
import System.Mem.Weak

data Data1 = Data1 {data1Chan_ :: Chan String}

type ReaderLoggingT r m a t = t (ReaderT r (LoggingT m)) a

type ReaderLogging1 m a = ReaderLoggingT Data1 m a IdentityT

runReaderLoggingT ::
  (MonadIO m) =>
  ReaderLoggingT r m a IdentityT ->
  r ->
  (Loc -> LogSource -> LogLevel -> LogStr -> IO ()) ->
  m a
runReaderLoggingT a r l =
  runLoggingT (runReaderT (runIdentityT a) r) l

someFunc :: IO ()
someFunc = do
  c <- liftIO newChan
  runStdoutLoggingT (runReaderT (runIdentityT someFunc2) (data1 c))
  where
    data1 c = Data1 {data1Chan_ = c}

forkDeRefWeakWriteChan :: (MonadIO m) => Weak (Chan String) -> ReaderLogging1 m ()
forkDeRefWeakWriteChan c = do
  $logInfo "before threadDelay"
  liftIO (deRefWeak c)
    >>= ( \case
            Just c' -> do
              -- at this time, it's fine.
              $logInfo "deRefWeak 1 success."
              liftIO (writeChan c' "it's ok.")
            Nothing -> $logInfo "deRefWeak 1 fail."
        )
  liftIO (threadDelay (1000 * 1000))
  $logInfo "after threadDelay"
  liftIO (deRefWeak c)
    >>= ( \case
            Just c' -> do
              -- I expect that this should be executed too.
              $logInfo "deRefWeak 2 success."
              liftIO (writeChan c' "it's ok too.")
            Nothing ->
              -- but, this was executed when "stack run".
              $logInfo "deRefWeak 2 fail."
        )

forkReadChan :: (MonadIO m) => ReaderLogging1 m ()
forkReadChan = do
  r <- ask
  l <- askLoggerIO
  c' <- liftIO (mkWeakPtr (data1Chan_ r) Nothing)
  $logInfo "before forkIO"
  void (liftIO (forkIO (runReaderLoggingT (forkDeRefWeakWriteChan c') r l)))
  $logInfo "before readChan 1"
  ret <- liftIO (readChan (data1Chan_ r))
  $logInfo (DT.pack ("after readChan 1. " ++ ret))
  $logInfo "before readChan 2"
  ret' <- liftIO (readChan (data1Chan_ r))
  $logInfo (DT.pack ("after readChan 2. " ++ ret'))

someFunc2 :: (MonadIO m) => ReaderLogging1 m ()
someFunc2 = do
  r <- ask
  l <- askLoggerIO
  liftIO $ do
    -- in this test code,
    -- because readChan doesn't throw BlockedIndefinitelyOnMVar,
    -- I assumed that 1 < the Chan's refcount.
    -- the key point of question is that if 1 < the Chan's refcount,
    -- why did deRefWeak return Nothing instead of Just?
    -- or, if I did something wrongly or my assumption was wrong, please let me know.
    void (forkIO (void (runReaderLoggingT forkReadChan r l)))
    void getLine