    {-# LANGUAGE TypeFamilies #-}
    {-# LANGUAGE FlexibleInstances #-}
    {-# LANGUAGE FlexibleContexts #-}
    module Readerize where

    import Control.Monad.Reader

    type family Readerize r where
      Readerize (a -> IO r) = ReaderT a IO r
      Readerize (a -> b -> r) = b -> Readerize (a -> r)
    
    class Readerizable r where
      readerize :: r -> Readerize r

    instance Readerizable (a -> IO r) where
      readerize = ReaderT

    instance Readerizable (a -> r) => Readerizable (a -> b -> r) where
      readerize f = readerize . flip f

    example1 :: Int -> IO String
    example1 = undefined

    result1 :: ReaderT Int IO String
    result1 = readerize example1

    example2 :: (Show a) => Int -> a -> Bool -> IO String
    example2 = undefined

    result2 :: (Show a) => a -> Bool -> ReaderT Int IO String
    result2 = readerize example2

    example3 :: a -> b -> c -> d -> IO e
    example3 = undefined

    result3 :: c -> d -> ReaderT (a,b) IO e
    result3 = readerize (uncurry example3)

