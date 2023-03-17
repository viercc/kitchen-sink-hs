{-# LANGUAGE DeriveTraversable #-}
module GameTree where

data Nat = Zero | Succ Nat
    deriving (Eq, Show)

instance Ord Nat where
  compare Zero Zero = EQ
  compare (Succ _) Zero = GT
  compare Zero (Succ _) = LT
  compare (Succ a) (Succ b) = compare a b

  Zero <= _ = True
  Succ _ <= Zero = False
  Succ a <= Succ b = a <= b

  min Zero _ = Zero
  min (Succ _) Zero = Zero
  min (Succ a) (Succ b) = Succ (min a b)

  max Zero b = b
  max (Succ a') b = Succ $ case b of
    Zero -> a'
    Succ b' -> max a' b'

infNat :: Nat
infNat = Succ infNat

data GameTree f g s = GameTree { _gameState :: s,  _children :: f (GameTree g f s) }
  deriving (Functor, Foldable, Traversable)

annotate :: (Functor f, Functor g) => (s -> f m -> m) -> (s -> g m -> m) -> GameTree f g s -> GameTree f g (s, m)
annotate aggF aggG = goF
  where
    goF (GameTree s children) =
      let children' = goG <$> children
          m = aggF s (snd . _gameState <$> children')
       in GameTree (s, m) children'
    goG (GameTree s children) =
      let children' = goF <$> children
          m = aggG s (snd . _gameState <$> children')
       in GameTree (s, m) children'

-- | Game is eventually won by player f.
--   
--   * f is trying to win as fast as possible
--   * g is trying to delay the loss as long as possible
annotateMinMaxTurns :: (Functor f, Foldable f, Functor g, Foldable g) => (s -> Bool) -> GameTree f g s -> GameTree f g (s, Nat)
annotateMinMaxTurns isWin = annotate aggF aggG
  where
    aggF s children
      | isWin s = Zero
      | otherwise = Succ (minimumNat children)
    aggG _ = maximumNat

minimumNat :: Foldable f => f Nat -> Nat
minimumNat = foldr min infNat

maximumNat :: Foldable f => f Nat -> Nat
maximumNat = foldr max Zero