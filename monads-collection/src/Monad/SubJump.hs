{-# LANGUAGE GADTs#-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Monad.SubJump(
    SubT, runSubT,
    Label(), sub, sub_, label, jump, jump_, callCC
) where

import Control.Monad.Trans.Free

import Unsafe.Coerce (unsafeCoerce)
import GHC.Exts (Any)
import Control.Monad.Trans (MonadTrans (..))

newtype Label s t = Label Int
type role Label nominal nominal

data SubF s a where
    Sub :: (Label s t -> a) -> (t -> a) -> SubF s a
    Jump :: Label s t -> t -> SubF s a

instance Functor (SubF s) where
    fmap f (Sub p q) = Sub (f . p) (f . q)
    fmap _ (Jump l t) = Jump l t

newtype SubT s m a = SubT { unwrapSubT :: FreeT (SubF s) m a }
    deriving newtype (Functor, Applicative, Monad, MonadTrans)

runSubT :: Monad m => (forall s. SubT s m a) -> m a
runSubT tma = runSubT' emptyTable (unwrapSubT tma)

runSubT' :: Monad m => JumpTable s (m a) -> FreeT (SubF s) m a -> m a
runSubT' table (FreeT mfa) = do
    fa <- mfa
    case fa of
        Pure a -> pure a
        Free (Sub p q) -> 
            let cont = runSubT' table' . q
                (label', table') = addLabel cont table
            in runSubT' table' (p label')
        Free (Jump l t) -> at table l t

sub :: Monad m => (Label s t -> SubT s m a) -> (t -> SubT s m a) -> SubT s m a
sub f g = SubT $ wrap (Sub (unwrapSubT . f) (unwrapSubT . g))

sub_ :: Monad m => (Label s () -> SubT s m a) -> SubT s m a -> SubT s m a
sub_ f g = sub f (const g)

label :: Monad m => SubT s m (Either (Label s t) t)
label = sub (pure . Left) (pure . Right)

jump :: Monad m => Label s t -> t -> SubT s m a
jump l t = SubT $ liftF (Jump l t)

jump_ :: Monad m => Label s () -> SubT s m a
jump_ l = jump l ()

callCC :: Monad m => ((forall b. a -> SubT s m b) -> SubT s m a) -> SubT s m a
callCC body = sub (\l -> body (jump l)) pure

-- * Unsafe things

data JumpTable s r = JumpTable !Int [Any -> r]

emptyTable :: JumpTable s r
emptyTable = JumpTable 0 []

addLabel :: (t -> r) -> JumpTable s r -> (Label s t, JumpTable s r)
addLabel cont (JumpTable n ks) = (Label n, JumpTable (succ n) (unsafeCoerce cont : ks))

at :: JumpTable s r -> Label s t -> t -> r
at (JumpTable n ks) (Label l)
   | l < n = (ks !! (n - l - 1)) . unsafeCoerce
   | otherwise = error $ "bad label: " ++ show l

--------

ex1 :: SubT s IO ()
ex1 = do
   sub (\l -> lift (putStr "input>" >> getLine) >>= jump l >> lift (putStrLn "this is unreachable"))
       (\ps -> lift (putStrLn ("your_input=" ++ show ps)))

newtype LoopLabel s = Loop (Label s (LoopLabel s))

gotoLabel :: Monad m => SubT s m (LoopLabel s)
gotoLabel = sub (pure . Loop) pure

goto :: Monad m => LoopLabel s -> SubT s m a
goto (Loop l) = jump l (Loop l)

ex2 :: SubT s IO ()
ex2 =
  flip sub_ (lift $ putStrLn "End.")
    \exitLabel -> do
        loopLabel <- gotoLabel
        answer <- lift $ putStr "Do you want to exit? " >> getLine
        if answer == "yes" then jump_ exitLabel else goto loopLabel