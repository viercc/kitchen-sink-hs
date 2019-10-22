{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
module Control.Monad.Queue(
    Queue(),
    getLength,
    offer,
    offer1,
    poll,
    poll1,
    peek,

    traceQueue,
    evalQueue,
    execQueue,
    runQueue
) where

import Data.Foldable
import Data.Functor.Identity
import Control.Monad

newtype Queue c a =
    Queue { unQueue :: forall r. Int -> [c] -> (a -> Int -> [c] -> ([c], r)) -> ([c], r) }
    deriving (Functor)

instance Applicative (Queue c) where
  pure = return
  (<*>) = ap

instance Monad (Queue c) where
  return a = Queue $ \n is k -> k a n is
  qa >>= f = Queue $ \n is k ->
    unQueue qa n is $ \a n' is' ->
      unQueue (f a) n' is' k

-- | Get the current length of the queue.
getLength :: Queue c Int
getLength = Queue $ \n is k -> k n n is

-- | Add items to the right side of the queue.
offer :: (Foldable f) => f c -> Queue c ()
offer cs = Queue $ \n is k ->
    let !n' = n + length cs
        ~(rest, result) = k () n' is
    in (toList cs ++ rest, result)

offer1 :: c -> Queue c ()
offer1 = offer . Identity

-- | @poll m@ removes @m@ items from left of the queue.
--   then return removed items in order.
--   If the length of the queue is smaller than @m@, it removes
--   all remaining items.
poll :: Int -> Queue c [c]
poll m = Queue $ \n is k ->
    let d = min m n
        !n' = n - d
        (removedElems, is') = splitAt d is
    in k removedElems n' is'

poll1 :: Queue c (Maybe c)
poll1 = list2Maybe <$> poll 1
  where
    list2Maybe [] = Nothing
    list2Maybe (c:_) = Just c

-- | @peek m@ gets @m@ items from left of the queue,
--   without removing them.
--   If the length of the queue is smaller than @m@, it returns
--   all remaining items.
peek :: Int -> Queue c [c]
peek m = Queue $ \n is k ->
    let d = min m n
    in k (take d is) n is

-- | Run @Queue@ with initially empty queue. Return the trace, which is
--   all items added to queue throughout the computation.
--
--   Example:
--   
--   >>> traceQueue $ offer "abcde" >> poll 2 >> offer "fg" >> poll 4
--   "abcdefg"
traceQueue :: Queue c a -> [c]
traceQueue qa =
    let (queue,_) = unQueue qa 0 queue (\_ _ _ -> ([], ()))
    in queue

-- | Run @Queue@ with initially empty queue. Return the final state of the queue.
--   
--   Example:
--   
--   >>> execQueue $ offer "abcde" >> poll 2 >> offer "fg" >> poll 4
--   "g"
execQueue :: Queue c a -> [c]
execQueue qa =
  let (queue, is) = unQueue qa 0 queue (\_ _ is' -> ([], is'))
  in is

-- | Run @Queue@ with initially empty queue. Return the computation result.
--   
--   Example:
--   
--   >>> evalQueue $ offer "abcde" >> poll 2 >> offer "fg" >> poll 4
--   "cdef"
evalQueue :: Queue c a -> a
evalQueue qa =
  let (queue, a) = unQueue qa 0 queue (\a' _ _ -> ([], a'))
  in a

-- | Run @Queue@ with initially empty queue. Return the trace, final state of the queue,
--   and the computation result.
--   
--   Example:
--   
--   >>> runQueue $ offer "abcde" >> poll 2 >> offer "fg" >> poll 4
--   ("abcdefg","g","cdef")
runQueue :: Queue c a -> ([c], [c], a)
runQueue qa =
  let (queue, (is, a)) = unQueue qa 0 queue (\a' _ is' -> ([], (is', a')))
  in (queue, is, a)
