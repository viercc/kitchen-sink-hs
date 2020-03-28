#!/usr/bin/env cabal
{- cabal:
build-depends: base, containers, data-memocombinators
-}
{-

https://www.reddit.com/r/math/comments/8seqeh/calculating_probability_for_a_dnd_dice_minigame/

Quoting the post:

Hello all,

I play DnD, which is a tabletop game that revolves around using dice. I came up with an idea for a very quick die-based minigame that could be used for gambling, etc.

I'm basically just looking for feedback on how random this game is, if it already exists in some form that I can copy rules from, and what measures I could introduce to narrow the range of possible results. I'll expand below.

You roll 4 6-sided die, getting a random result out of 936 possible combinations. In this test case, 1, 2, 4, 5.

Then, you try to use the rolled totals to cancel each other out. 1+4 =5, cancelling out the 1, 4 and 5. This leaves the 2, which becomes that players score for the round. The goal is to have the lowest total score after 3 rounds.

Now comes the catch: DnD has a concept called "proficiency", which can gives characters an in-game boost to certain things, including dice games. What measures can I introduce for players with this ability to make their success more likely, but not guaranteed? Some ideas I had were:

    Being able to change the value of a single die by 1 point, up or down (e.g. 5>4 or 5>6).
    Being able to roll 4 rounds, and take the best 3 as their total.
    Being able to re-roll 1 of the 4 die.

My trouble is, I have no idea how to calculate how these measures will affect the player's probability of winning! Any help with this will be greatly appreciated.


-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor  #-}
module Main where

import Data.Bifunctor (Bifunctor(..))
import Data.Semigroup
import Data.List (minimumBy, sort)
import Data.Ratio
import Data.Tuple (swap)
import Data.Ord (comparing)
import qualified Data.Map as Map

import Control.Monad (ap)

import qualified Data.MemoCombinators as Memo

---------------------------------------

newtype Bag a = Bag [a]
  deriving (Show, Eq, Ord, Foldable)

fromList :: (Ord a) => [a] -> Bag a
fromList = Bag . sort

toList :: Bag a -> [a]
toList (Bag as) = as

foldMapSplits :: (Monoid r) => (a -> r) -> [a] -> [(r,r)]
foldMapSplits f = go
  where
    go [] = [(mempty, mempty)]
    go (a:as) =
      let rest = go as
          fa = f a
      in map (first (mappend fa)) rest ++ map (second (mappend fa)) rest

splitsWithSum :: (Num a) => Bag a -> [(Bag a, a, Bag a, a)]
splitsWithSum = map final . foldMapSplits f . toList
  where
    f a = ([a], Sum a)
    final ((bs, Sum sumBs), (cs, Sum sumCs)) = (Bag bs, sumBs, Bag cs, sumCs)

cancelOut :: (Ord a, Integral a) => Bag a -> (a, Bag a, Bag a, Bag a)
cancelOut as = minimum
  [ (sumBs, bs, c1s, c2s)
    | (bs, sumBs, cs, sumCs) <- splitsWithSum as
    , even sumCs
    , (c1s, sumC1s, c2s, sumC2s) <- splitsWithSum cs
    , sumC1s == sumC2s ]

score :: (Ord a, Integral a) => Bag a -> a
score as = case cancelOut as of
  (s, _, _, _) -> s

merge :: (Ord a) => Bag a -> Bag a -> Bag a
merge = \(Bag as) (Bag bs) -> Bag (go as bs)
  where
    go as [] = as
    go [] bs = bs
    go as@(a:as') bs@(b:bs') =
      if a <= b
        then a : go as' bs
        else b : go as bs'

insert :: (Ord a) => a -> Bag a -> Bag a
insert a = merge (Bag [a])

---------------------------------------

newtype Prob a = Prob { getTable :: [(Rational, a)] }
  deriving (Show, Eq, Ord, Functor)

instance Applicative Prob where
  pure = return
  (<*>) = ap

instance Monad Prob where
  return a = Prob [(1,a)]
  Prob ma >>= k = Prob $
    do (pa, a) <- ma
       (pb, b) <- getTable $ k a
       return (pa * pb, b)

aggregate :: (Ord a) => Prob a -> Prob a
aggregate =
  Prob . map swap .
  Map.toList . Map.fromListWith (+) .
  map swap . getTable

expectation :: (Real b, Fractional r) => Prob a -> (a -> b) -> r
expectation (Prob as) f =
  sum [ fromRational (pa * toRational (f a)) | (pa, a) <- as ]


coin :: Prob Int
coin = Prob [(1%2, 0), (1%2, 1)]

-- O(2^n)
slowCountHeads :: Int -> Prob Int
slowCountHeads n
  | n <= 0    = return 0
  | otherwise = aggregate $
      do x <- coin
         sumXs <- slowCountHeads (n - 1)
         return $ x + sumXs

-- O(n^2)
fastCountHeads :: Int -> Prob Int
fastCountHeads n
  | n <= 0    = return 0
  | otherwise = aggregate $ (+) <$> coin <*> fastCountHeads (n-1)

---------------------------------------

d6 :: Prob Int
d6 = Prob $ zip (repeat (1 % 6)) [1..6]

d6666 :: Prob (Bag Int)
d6666 = aggregate $
  fromList <$> sequenceA (replicate 4 d6)

-- memoized score
score' :: Bag Int -> Int
score' = Memo.wrap Bag unBag memoListInt score
  where memoListInt = Memo.list Memo.integral
        unBag (Bag as) = as

noProficiency1 :: Prob Int
noProficiency1 = aggregate $ score' <$> d6666

baseExpectedScore1 :: Double
baseExpectedScore1 = expectation noProficiency1 id


{-
   Nimble proficiency: Can change the value of any one dice by 1 point.
   Only use up to once during 3 rounds.

   Strategy:
     During first two round, given that round's dice roll, if using
     best nimble move improves the score more than 2, do it.
     At last round, always try to do nimble.
     
     To perform a nimble, consider every move of nimble possible, and
     choose best one.
-}

nimbleExpectedScore :: Double
nimbleExpectedScore =
  expectation nimbleProficiency id

nimbleProficiency :: Prob Int
nimbleProficiency =
  do (score1'', used1) <- aggregate $
       do try1 <- d6666
          let score1 = score' try1
              (score1', _) = nimbleStrategy try1
              used1 = fromIntegral (score1 - score1') >= nimbleExpectedImprovement
              score1'' = if used1 then score1' else score1
          return (score1'', used1)
     (score2'', used2) <- aggregate $
       do try2 <- d6666
          let score2 = score' try2
              (score2', _) = nimbleStrategy try2
              used2 = used1 || fromIntegral (score2 - score2') >= nimbleExpectedImprovement
              score2'' = if not used1 && used2 then score2' else score2
          return (score2'', used2)
     score3'' <- aggregate $
       do try3 <- d6666
          let score3 = score' try3
              (score3', _) = nimbleStrategy try3
              score3'' = if not used2 then score3' else score3
          return score3''
     return (score1'' + score2'' + score3'')

nimbleExpectedImprovement :: Double
nimbleExpectedImprovement =
  baseExpectedScore1 - 
  expectation nimbleProficiency1 id

nimbleProficiency1 :: Prob Int
nimbleProficiency1 = aggregate $
  (fst . nimbleStrategy) <$> d6666

nimbleStrategy :: Bag Int -> (Int, Bag Int)
nimbleStrategy = minimumBy (comparing fst) . map (\s -> (score' s, s)) . nimbleMoves . toList
  where
    nimbleMoves [] = [Bag []]
    nimbleMoves (a:as) = case a of
      1 -> insert 2 (Bag as) : map (insert a) (nimbleMoves as)
      6 -> insert 5 (Bag as) : map (insert a) (nimbleMoves as)
      _ -> insert (a-1) (Bag as) :
           insert (a+1) (Bag as) :
           map (insert a) (nimbleMoves as)

{- Reroll proficiency: Can reroll any one dice after d6666 is thrown.
   Only use up to once during 3 rounds.

   Strategy:
     During first two round, given that round's dice roll, if using
     reroll improves expected score more than average improvement of
     one round, do reroll.
     At last round, always try to reroll.

     To perform a reroll, calculate expected score of each four dice rerolled,
     compare them and no-reroll case. Choose best dice to reroll then.
-}

rerollExpectedScore :: Double
rerollExpectedScore =
  expectation rerollProficiency id

rerollProficiency :: Prob Int
rerollProficiency =
  do (score1'', used1) <- aggregate $
       do try1 <- d6666
          let score1 = score' try1
              (score1', reroll1) = rerollStrategy try1
              used1 = (fromIntegral score1 - score1') >= rerollExpectedImprovement
          score1'' <- if used1 then score' <$> reroll1
                               else return score1
          return (score1'', used1)
     (score2'', used2) <- aggregate $
       do try2 <- d6666
          let score2 = score' try2
              (score2', reroll2) = rerollStrategy try2
              used2 = used1 || (fromIntegral score2 - score2') >= rerollExpectedImprovement
          score2'' <- if not used1 && used2
            then score' <$> reroll2
            else return score2
          return (score2'', used1)
     score3'' <- aggregate $
       do try3 <- d6666
          let score3 = score' try3
              (_, reroll3) = rerollStrategy try3
          if not used2
            then score' <$> reroll3
            else return score3
     return (score1'' + score2'' + score3'')

rerollProficiency1 :: Prob Int
rerollProficiency1 = aggregate $
  do as <- d6666
     bs <- snd $ rerollStrategy as
     return $ score' bs

rerollExpectedImprovement :: Double
rerollExpectedImprovement =
  baseExpectedScore1 - 
  expectation rerollProficiency1 id

rerollStrategy :: Bag Int -> (Double, Prob (Bag Int))
rerollStrategy (Bag as) = minimumBy (comparing fst) stratScores
  where
    strats = map (fmap fromList) (rerollChoices as)
    stratScores = map (\s -> (expectation s score', s)) strats
    
    rerollChoices [] = [return []]
    rerollChoices (x:xs) =
      fmap (:xs) d6 : map (fmap (x:)) (rerollChoices xs)

{-
  Foresee proficiency: Instead of doing 3 rounds, do 4 rounds and
  ignore worst round.
-}

foreseeExpectedScore :: Double
foreseeExpectedScore = expectation foreseeProficiency id

foreseeProficiency :: Prob Int
foreseeProficiency =
  do scores <- sequenceA (replicate 4 noProficiency1)
     return (sum scores - maximum scores)

main :: IO ()
main =
  do putStrLn $ "[none]:    " ++ show (3 * baseExpectedScore1)
     putStrLn $ "[nimble]:  " ++ show nimbleExpectedScore
     putStrLn $ "[reroll]:  " ++ show rerollExpectedScore
     putStrLn $ "[foresee]: " ++ show foreseeExpectedScore
