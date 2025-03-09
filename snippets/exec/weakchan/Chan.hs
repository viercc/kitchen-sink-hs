{-# LANGUAGE CPP #-}
module Chan(
  Chan, newChan, writeChan, readChan, dupChan, dupChanR,
  ReadChan(), WriteChan(),
  WeakWriteChan(), toWeakWriteChan, writeWeakChan
) where

import Control.Exception (mask_)
import Control.Concurrent.MVar
import System.Mem.Weak ( deRefWeak, Weak )

#define _UPK_(x) {-# UNPACK #-} !(x)

-- A channel is represented by two @MVar@s keeping track of the two ends
-- of the channel contents, i.e., the read- and write ends. Empty @MVar@s
-- are used to handle consumers trying to read from an empty channel.

-- | 'Chan' is a pair of 'ReadChan' and 'WriteChan'.
type Chan a = (ReadChan a, WriteChan a)

-- | Only the reader half of a channel.
newtype ReadChan a = ReadChan (MVar (Stream a))
  deriving Eq

-- | Only the write half of a channel.
newtype WriteChan a = WriteChan (MVar (Stream a))
  deriving Eq

type Stream a = MVar (ChItem a)

data ChItem a = ChItem a _UPK_(Stream a)
  -- benchmarks show that unboxing the MVar here is worthwhile, because
  -- although it leads to higher allocation, the channel data takes up
  -- less space and is therefore quicker to GC.

-- See the Concurrent Haskell paper for a diagram explaining
-- how the different channel operations proceed.

-- @newChan@ sets up the read and write end of a channel by initialising
-- these two @MVar@s with an empty @MVar@.

-- |Build and return a new instance of 'Chan'.
newChan :: IO (Chan a)
newChan = do
   hole  <- newEmptyMVar
   readVar  <- newMVar hole
   writeVar <- newMVar hole
   return (ReadChan readVar, WriteChan writeVar)

-- To put an element on a channel, a new hole at the write end is created.
-- What was previously the empty @MVar@ at the back of the channel is then
-- filled in with a new stream element holding the entered value and the
-- new hole.

-- | Write a value to a 'WriteChan'.
writeChan :: WriteChan a -> a -> IO ()
writeChan (WriteChan writeVar) val = do
  new_hole <- newEmptyMVar
  mask_ $ do
    old_hole <- takeMVar writeVar
    putMVar old_hole (ChItem val new_hole)
    putMVar writeVar new_hole

-- The reason we don't simply do this:
--
--    modifyMVar_ writeVar $ \old_hole -> do
--      putMVar old_hole (ChItem val new_hole)
--      return new_hole
--
-- is because if an asynchronous exception is received after the 'putMVar'
-- completes and before modifyMVar_ installs the new value, it will set the
-- Chan's write end to a filled hole.

-- | Read the next value from the 'ReadChan'. Blocks when the channel is empty. Since
-- the read end of a channel is an 'MVar', this operation inherits fairness
-- guarantees of 'MVar's (e.g. threads blocked in this operation are woken up in
-- FIFO order).
--
-- Throws 'Control.Exception.BlockedIndefinitelyOnMVar' when the channel is
-- empty and no other thread holds a reference to the channel.
readChan :: ReadChan a -> IO a
readChan (ReadChan readVar) = 
  modifyMVar readVar $ \read_end -> do
    (ChItem val new_read_end) <- readMVar read_end
        -- Use readMVar here, not takeMVar,
        -- else dupChan doesn't work
    return (new_read_end, val)

-- | Duplicate a channel (from the write channel): the duplicate channel begins empty, but data written to
-- either channel from then on will be available from both. Hence this creates
-- a kind of broadcast channel, where data written by anyone is seen by
-- everyone else.
dupChan :: WriteChan a -> IO (ReadChan a)
dupChan (WriteChan writeVar) = do
   hole       <- readMVar writeVar
   newReadVar <- newMVar hole
   return (ReadChan newReadVar)

dupChanR :: ReadChan a -> IO (ReadChan a)
dupChanR (ReadChan readVar) = do
   hole       <- readMVar readVar
   newReadVar <- newMVar hole
   return (ReadChan newReadVar)

-- | Only the writer half of a channel, but "weak": if no reader is alive,
--   the channel is garbage collected.
newtype WeakWriteChan a = WeakWriteChan (MVar (Weak (Stream a)))
  deriving Eq

toWeakWriteChan :: WriteChan a -> IO (WeakWriteChan a)
toWeakWriteChan (WriteChan writeVar) = do
  hole <- readMVar writeVar
  weakHole <- mkWeakMVar hole (pure ())
  weakVar <- newMVar weakHole
  return (WeakWriteChan weakVar)

-- | Attempts to write to the weak half-channel. Returns 'False' if the channel is already garbage collected.
writeWeakChan :: WeakWriteChan a -> a -> IO Bool
writeWeakChan (WeakWriteChan weakVar) val = do
  new_hole <- newEmptyMVar
  new_weak_hole <- mkWeakMVar new_hole (pure ())
  mask_ $ do
    mHole <- takeMVar weakVar >>= deRefWeak
    case mHole of
      Just old_hole -> do
        putMVar old_hole (ChItem val new_hole)
        putMVar weakVar new_weak_hole
        return True
      Nothing -> return False
