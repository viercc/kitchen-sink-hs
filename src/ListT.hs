{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RankNTypes        #-}
module ListT where

import           Control.Monad.ST
import           Control.Monad.ST.Unsafe (unsafeInterleaveST)

import           Data.STRef

-- | \"ListT done right\".
newtype ListT m a = ListT { runListT :: m (ListF a (ListT m a)) }

data ListF a r = Nil | Cons a r
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

-- | Convert to a list by evaluating everything at once.
toList :: (Monad m) => ListT m a -> m [a]
toList = fmap reverse . loop []
  where
    loop accum xs = runListT xs >>= \case
      Nil        -> return accum
      Cons x xs' -> loop (x:accum) xs'

-- | Lazy version of 'toList' from @ListT (ST s)@.
toListLazily :: (forall s. ListT (ST s) a) -> [a]
toListLazily xs = runST (loop xs)
  where loop as = runListT as >>= \case
          Nil        -> return []
          Cons a as' -> (a :) <$> unsafeInterleaveST (loop as')

test :: ListT (ST s) Int
test = ListT $
  do ref <- newSTRef 0
     let loop =
           do i <- readSTRef ref
              writeSTRef ref $! (i+1)
              return (Cons i (ListT loop))
     loop

{-
take 10 $ runST (toList test)  -- don't terminate
take 10 $ runListLazily test   -- works
-}

