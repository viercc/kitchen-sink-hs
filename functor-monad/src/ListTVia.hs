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
module ListTVia where

import Data.Kind ( Type )
import Control.Monad.Trans.Class
import Control.Monad.Trans.Free hiding (type FreeT())

import Data.Monoid (Ap(..))

import FMonad.FreeT
import FMonad.Trail

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
collapse :: Monad m => ListT m () -> m ()
collapse = iterT (\((), m) -> m) . unwrapFreeT . runListT

eval :: Show a => ListT IO a -> IO ()
eval ma = collapse (ma >>= (lift . pr))
  where pr a = putStrLn $ "ValueProduced[" ++ show a ++ "]"

test1, test2, test3 :: ListT IO Int
test1 = lift (print "A") >> mempty
test2 = lift (print "B") >> pure 1
test3 = lift (print "C") >> (pure 2 <> pure 3)

