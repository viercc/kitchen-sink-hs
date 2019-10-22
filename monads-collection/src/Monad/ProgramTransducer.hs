{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Monad.ProgramTransducer where

import Data.IORef

type Tr f g = forall r. (forall a. g a -> (a -> r) -> r) -> (forall b. f b -> (b -> r) -> r)

toMonad :: (Monad g) => Tr f g -> f a -> g a
toMonad tr fa = tr (>>=) fa return

composeTr :: Tr f g -> Tr g h -> Tr f h
composeTr tfg tgh steph = tfg (tgh steph)

liftNatural :: (forall a. f a -> g a) -> Tr f g
liftNatural p handleG fb = handleG (p fb)

------------------------------------

{- ===============================
                Example
   ===============================  -}

data StateCmd s a where
    Put :: s -> StateCmd s ()
    Get :: StateCmd s s

data CandyCmd a where
    -- | @TakeCandy n@ takes out n candies from the bag. Reduce number of
    --   candies up to @n@.
    --   Number of candies can't be negative.
    --   Returns actual number of candies you got.
    TakeCandy :: Int -> CandyCmd Int
    -- | @PutCandy n@ puts n candies in the bag.
    PutCandy :: Int -> CandyCmd ()

stateViaIORef :: forall s. IORef s -> Tr (StateCmd s) IO
stateViaIORef ref = liftNatural $ \stateCmd ->
    case stateCmd of
        Put s -> writeIORef ref s
        Get   -> readIORef ref

candy2state :: Tr CandyCmd (StateCmd Int)
candy2state handleState fb returnB =
    case fb of
        TakeCandy n ->
            handleState Get $ \numCandy ->
            let tookCandies = min n numCandy in
            handleState (Put (numCandy - tookCandies)) $ \() ->
            returnB tookCandies
        PutCandy n ->
            handleState Get $ \numCandy ->
            handleState (Put (n + numCandy)) returnB
