{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}

module MonadLaws
  ( Enum1,
    Var, skolem1, skolem2, skolem3,
    propMonadUnitL,
    propMonadUnitR,
    propMonadAssoc,
    checkMonad,
    checkMonadIO,
  )
where

import Control.Applicative
import Control.Monad (join)
import Control.Monad.State ( evalState, MonadState(state), State )
import Data.Functor.Compose ( Compose(..) )

type Enum1 m = forall f a. (Alternative f) => f a -> f (m a)

type E = Compose [] (State Int)

type Var = Int

var :: E Var
var = Compose [state (\n -> n `seq` (n, n + 1))]

eval :: E r -> [r]
eval = fmap (flip evalState 0) . getCompose

skolem1 :: Enum1 m -> [m Var]
skolem1 enum1 = eval $ enum1 var

skolem2 :: Enum1 m -> [m (m Var)]
skolem2 enum1 = eval $ enum1 (enum1 var)

skolem3 :: Enum1 m -> [m (m (m Var))]
skolem3 enum1 = eval $ enum1 (enum1 (enum1 var))

----------------

propMonadUnitL ::
  forall m.
  (Monad m, forall b. Eq b => Eq (m b)) =>
  m Var ->
  Bool
propMonadUnitL mx = join (return mx) == mx

propMonadUnitR ::
  forall m.
  (Monad m, forall b. Eq b => Eq (m b)) =>
  m Var ->
  Bool
propMonadUnitR mx = (mx >>= return) == mx

propMonadAssoc ::
  forall m.
  (Monad m, forall b. Eq b => Eq (m b)) =>
  m (m (m Var)) ->
  Bool
propMonadAssoc mmmx = join (join mmmx) == join (fmap join mmmx)

----------------

checkMonad ::
  forall m.
  (Monad m, forall b. Eq b => Eq (m b)) =>
  Enum1 m ->
  Bool
checkMonad enum1 =
  and
    [ all propMonadUnitL (skolem1 enum1),
      all propMonadUnitR (skolem1 enum1),
      all propMonadAssoc (skolem3 enum1)
    ]

checkMonadIO ::
  forall m.
  ( Monad m,
    forall b. Eq b => Eq (m b),
    forall b. Show b => Show (m b)
  ) =>
  Enum1 m ->
  IO Bool
checkMonadIO enum1 =
  case counterExamples of
    [] -> return True
    (bad : _) -> do
      putStrLn "Counterexample:"
      putStrLn bad
      return False
  where
    counterExamples = badUnitL ++ badUnitR ++ badAssoc
    badUnitL =
      [ "join . return $" ++ show mx ++ " = " ++ show mx'
        | mx <- skolem1 enum1,
          let mx' = join (return mx),
          mx /= mx'
      ]
    badUnitR =
      [ "join . fmap return $" ++ show mx ++ " = " ++ show mx'
        | mx <- skolem1 enum1,
          let mx' = mx >>= return,
          mx /= mx'
      ]
    badAssoc =
      [ "mmmx = "
          ++ show mmmx
          ++ "\n"
          ++ "join . join      $ mmmx = "
          ++ show mx1
          ++ "\n"
          ++ "join . fmap join $ mmmx = "
          ++ show mx2
        | mmmx <- skolem3 enum1,
          let mx1 = join (join mmmx)
              mx2 = join (fmap join mmmx),
          mx1 /= mx2
      ]
