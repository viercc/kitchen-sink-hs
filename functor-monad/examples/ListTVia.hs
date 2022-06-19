{-# LANGUAGE
  StandaloneKindSignatures,
  DerivingVia,
  DerivingStrategies,
  DeriveFunctor,
  StandaloneDeriving,
  RankNTypes,
  ScopedTypeVariables,
  InstanceSigs,
  TypeOperators,
  TupleSections,
  QuantifiedConstraints
#-}
module Main(main) where

import Data.Kind ( Type )
import Control.Monad.Trans.Class
import Control.Monad.Trans.Free hiding (type FreeT())

import Data.Monoid (Ap(..))

import FMonad.FreeT
import Control.Monad.Trail

type    ListT :: (Type -> Type) -> (Type -> Type)
newtype ListT m a = ListT { runListT :: FreeT ((,) a) m () }
    deriving stock (Eq, Ord, Show, Read)
    deriving (Functor, Applicative, Monad)
        via (Trail (FreeT' m))
    deriving (Semigroup, Monoid)
        via (Ap (FreeT ((,) a) m) ())

-- MonadTrans is specific to ListT
instance MonadTrans ListT where
  lift ma = ListT . WrapFreeT . FreeT $ ma >>= \a -> return $ Free (a, return ())

-- For test:
forEach :: Monad m => ListT m a -> (a -> m ()) -> m ()
forEach as f = iterT (\(a, m) -> f a >> m) . unwrapFreeT . runListT $ as

test1, test2, test3 :: ListT IO Int
test1 = lift (putStrLn "SideEffect: A") >> mempty
test2 = lift (putStrLn "SideEffect: B") >> pure 1
test3 = lift (putStrLn "SideEffect: C") >> (pure 2 <> pure 3)

main :: IO ()
main = forEach test print
  where test = (test1 <> test2 <> test3) >>= \n -> pure 100 <> pure n
