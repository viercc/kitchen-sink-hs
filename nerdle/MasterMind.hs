{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveTraversable #-}
module MasterMind where

import Data.Functor.Rep
import Data.Bag qualified as Bag

import Data.Traversable
import Data.Foldable (toList)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Control.Monad (guard, join)
import Data.Monoid (Sum(..))
import Data.Bag (Bag)
import qualified Data.Set as Set

data Response =
      Hit  -- ^ Green in Wordle, Black peg in MasterMind
    | Blow -- ^ Yellow in Wordle, White peg in MasterMind
    | Miss -- ^ Grey in Wordle, no pegs in MasterMind
    deriving (Show, Read, Eq, Ord, Enum, Bounded)

-- Checks if the response is valid
response :: (Traversable v, Representable v, Ord char) => v char -> v char -> v Response
response xs ys = respBlows $ respHits xs ys

respHits :: (Representable v, Eq char) => v char -> v char -> v (Either Response (char, char))
respHits = liftR2 both
  where
    both x y | x == y    = Left Hit
             | otherwise = Right (x,y)

respBlows :: (Traversable v, Ord char) => v (Either Response (char, char)) -> v Response
respBlows rs =
    let letterCounts = Bag.fromList [ x | Right (x,_) <- toList rs ]
    in  snd $ mapAccumL step letterCounts rs
  where
    step lc resp = case resp of
        Left a       -> (lc, a)
        Right (x, y) -> case Bag.pullOut y lc of
            Nothing  -> (lc, Miss)
            Just lc' -> (lc', Blow)

data Uncertain a = Unknown | Known a
    deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

class Unifiable a where
  unify :: a -> a -> Maybe a

instance Eq a => Unifiable (Uncertain a) where
  unify Unknown uy = Just uy
  unify ux Unknown = Just ux
  unify (Known x) (Known y) | x == y    = Just (Known x)
                            | otherwise = Nothing

unifyVec :: (Traversable v, Representable v, Unifiable a) => v a -> v a -> Maybe (v a)
unifyVec x y = sequenceA $ liftR2 unify x y

responseToHint :: (Traversable v, Representable v, Ord c) => v c -> v Response -> Hint v c
responseToHint query resp = MkHint{ knownPos=knowns, possiblePos=poss, lowerCount=lowers, frozenChars = frozen }
  where
   qr = liftR2 (,) query resp
   knowns = (\(c,r) -> if r == Hit then Known c else Unknown) <$> qr
   lowers = Bag.fromList $ foldMap (\(c,r) -> [c | r /= Miss]) qr
   frozen = Set.fromList $ foldMap (\(c,r) -> [c | r == Miss]) qr
   poss = Map.fromListWith (liftR2 (&&)) [ (c,v) | (c, r) <- toList qr, r /= Miss, let v = possCond c <$> qr ]
   possCond c (c', Hit)  = c == c'
   possCond c (c', _)    = c /= c'

data Hint v c = MkHint { knownPos :: v (Uncertain c), possiblePos :: Table v c, lowerCount :: Bag c, frozenChars :: Set c }

type Table v c = Map c (v Bool)

popCount :: Foldable v => v Bool -> Int
popCount = getSum . foldMap (\b -> if b then 1 else 0)

noHint :: (Representable v) => Hint v c
noHint = MkHint{ knownPos = pureRep Unknown, possiblePos = Map.empty, lowerCount=Bag.empty, frozenChars=Set.empty}

mergeHint :: (Traversable v, Representable v, Ord c) => Hint v c -> Hint v c -> Maybe (Hint v c)
mergeHint h1 h2 = do
  knownPos' <- unifyVec (knownPos h1) (knownPos h2)
  let possiblePos' = Map.unionWith (liftR2 (&&)) (possiblePos h1) (possiblePos h2)
      lowerCount' = Bag.union (lowerCount h1) (lowerCount h2)
      frozenChars' = Set.union (frozenChars h1) (frozenChars h2)
  possiblePos' <- Just $ updateKnownPossible knownPos' possiblePos'
  guard $ all or possiblePos' -- All registered char must have at least one possible
  guard $ and (Map.intersectionWith (\lo candid -> lo <= popCount candid) (Bag.toFreqsMap lowerCount') possiblePos')

  pure $ MkHint knownPos' possiblePos' lowerCount' frozenChars'

updateKnownPossible :: (Traversable v, Representable v, Ord c) => v (Uncertain c) -> Table v c -> Table v c
updateKnownPossible known = Map.mapWithKey compatible
  where
    compatible c = liftR2 (\knownCell b -> b && all (== c) knownCell) known

propagateLimits :: (Traversable v, Representable v, Ord c) => Hint v c -> Maybe (Hint v c)
propagateLimits hint =
  do (needLoop, hint') <- propagateLimitsStep hint
     if needLoop
       then propagateLimits hint'
       else pure hint'

propagateLimitsStep :: (Traversable v, Representable v, Ord c) => Hint v c -> Maybe (Bool, Hint v c)
propagateLimitsStep hint@MkHint{ knownPos, possiblePos, lowerCount, frozenChars } = do
  frozenChars' <- case compare (Bag.size lowerCount) (length knownPos) of
    LT -> Just frozenChars
    EQ -> Just (frozenChars `Set.union` Map.keysSet (Bag.toFreqsMap lowerCount))
    GT -> Nothing
  
  let knownPosFromPossible = do
        (c,n) <- Bag.toFreqs lowerCount
        guard (c `Set.member` frozenChars')
        let v = possiblePos Map.! c
        pure $ fmap (\b -> if b then Known c else Unknown) v
  knownPos' <- foldr (\va mvb -> mvb >>= \vb -> unifyVec va vb) (Just $ pureRep Unknown) knownPosFromPossible
  if and (liftR2 (==) knownPos knownPos')
    then pure (frozenChars /= frozenChars', hint{frozenChars = frozenChars'})
    else do let possiblePos' = updateKnownPossible knownPos' possiblePos
            pure (True, hint{knownPos = knownPos', possiblePos = possiblePos', frozenChars = frozenChars'})
