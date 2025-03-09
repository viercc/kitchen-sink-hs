-- https://discourse.haskell.org/t/question-about-mkweakptr-and-derefweak/11509/3

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- to show deRefWeak's Noting result.

module Main (main) where


import Control.Monad.Reader (ask, ReaderT(..))
import Control.Monad.IO.Class (MonadIO(..))

import qualified Data.Text as DT
import qualified Data.Text.IO as DT.IO
import Chan
import Data.Foldable (for_)

import Control.Concurrent (threadDelay)

import Control.Concurrent.Async

data Data1 = Data1 {data1Chan_ :: Chan String }

type App = ReaderT Data1

main :: IO ()
main = do
  c <- newChan
  runReaderT someFunc2 (data1 c)
  where
    data1 c = Data1 {data1Chan_ = c}

logInfo' :: (MonadIO m) => DT.Text -> m ()
logInfo' = liftIO . DT.IO.putStrLn

writeProcess :: (MonadIO m) => WeakWriteChan String -> m ()
writeProcess c' = loop (1 :: Int)
  where
    loop i = do
      liftIO $ threadDelay (1000 * 1000)
      succeeded <- liftIO $ writeWeakChan c' ("<message " ++ show i ++ ">")
      if succeeded
        then do
          logInfo' $ DT.pack $ "success: write " ++ show i
          loop (i + 1)
        else logInfo' $ DT.pack $ "fail: write" ++ show i

readProcess :: (MonadIO m) => ReadChan String -> m ()
readProcess c = do
  for_ [1..3 :: Int] $ \i -> do
    ret <- liftIO (readChan c)
    logInfo' $ DT.pack $ "read(" ++ show i ++ "): " ++ ret

someFunc2 :: (MonadIO m) => App m ()
someFunc2 = do
  r <- ask
  let (rc, wc) = data1Chan_ r
  wc' <- liftIO $ toWeakWriteChan wc
  liftIO $ concurrently_ (writeProcess wc') (readProcess rc)