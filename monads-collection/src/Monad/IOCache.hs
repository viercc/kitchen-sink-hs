{-# LANGUAGE DeriveDataTypeable #-}
module Monad.IOCache (
  Cache(),
  request,
  requestCached,
  forkCache,

  CachedTaskFail(..)
) where

import Control.Monad.IO.Class
import Control.Monad.Reader

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Typeable
import Control.Exception

import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.MVar

data Cache k v = CacheEnv {
    localCache :: TVar (Map k v)
  , globalCache :: MVar (Map k v)
  }

instance Eq (Cache k v) where
  ce1 == ce2 = globalCache ce1 == globalCache ce2

data CachedTaskFail = CachedTaskFail
  deriving (Show, Read, Eq, Ord, Typeable)

instance Exception CachedTaskFail

newEmptyCache :: IO (Cache k v)
newEmptyCache = newCache Map.empty

newCache :: Map k v -> IO (Cache k v)
newCache initialCache =
  do lc <- newTVarIO initialCache
     gc <- newMVar initialCache
     return CacheEnv{ localCache = lc, globalCache = gc }

request :: (Ord k) => k -> IO v -> Cache k v -> IO (Maybe v)
request key heavyTask env =
  do lc <- readTVarIO (localCache env)
     case Map.lookup key lc of
       Just v -> return (Just v)
       Nothing -> do
         (gc', v) <- modifyMVar (globalCache env) $ \gc ->
           case Map.lookup key gc of
             Just v -> return (gc, (gc, Just v))
             Nothing -> do
               v <- catch (Just <$> heavyTask) $
                      \CachedTaskFail -> return Nothing
               let gc' = maybe id (Map.insert key) v gc
               return (gc', (gc', v))
         atomically $ writeTVar (localCache env) $! gc'
         return v

requestCached :: (Ord k) => k -> Cache k v -> IO (Maybe v)
requestCached key env =
  do lc <- readTVarIO (localCache env)
     case Map.lookup key lc of
       Just v -> return (Just v)
       Nothing -> do
         gc <- readMVar (globalCache env)
         atomically $ writeTVar (localCache env) gc
         return (Map.lookup key gc)

forkCache :: Cache k v -> (Cache k v -> IO ()) -> IO ThreadId
forkCache env threadAction =
  do lc <- readTVarIO $ localCache env
     forkIO $ do
       newLocalCache <- newTVarIO lc
       threadAction env{ localCache = newLocalCache }
