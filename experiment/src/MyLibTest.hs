{-# LANGUAGE DeriveFunctor #-}
module Main (main) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import Control.Comonad(Comonad(..), Cokleisli(..))

import Data.Profunctor

import Data.Void

-- W a = Traced m a, |m| = 3
data W a = W a a a
  deriving (Show, Functor)

this, that :: W a -> a
this (W a _ _) = a
that (W _ b _) = b

instance Comonad W where
    extract = this
    duplicate (W a b c) = W (W a b c) (W b c a) (W c a b)

-- ArrowApply law #2
--
-- first (arr (>>> h)) >>> app = app >>> h

main :: IO ()
main = do
    let lhs = runCokleisli (first (arr (>>> dump)) >>> app) ex
    let rhs = runCokleisli (app >>> dump) ex
    putStrLn $ "(LHS) = " ++ lhs
    putStrLn $ "(RHS) = " ++ rhs
    print $ lhs == rhs

ex :: W (Cokleisli W Char Char, Char)
ex = W (Cokleisli that, 'a') (Cokleisli this, 'b') (Cokleisli this, 'c')

dump :: Show a => Cokleisli W a String
dump = Cokleisli show

left'' :: Comonad f => Cokleisli f a b -> Cokleisli f (Either a c) (Either b c)
left'' (Cokleisli f) = Cokleisli (\fac ->
  case extract fac of
    Right c -> Right c
    Left a -> Left . f $ fmap (either id (const a)) fac)

-- choice law
-- x :: p a b
--   (unit)
--   id ≡ dimap voidE unvoidE . left'
--   
--       rmap Left = rmap Left . dimap voidE unvoidE . left'
--                 = dimap Left id . left'
--                 = lmap Left . left'
--   (assoc)
--   left' . left' ≡ dimap assocE unassocE . left'

-- Isomorphism (voidE, unvoidE)
voidE :: a -> Either a Void
voidE = Left
unvoidE :: Either a Void -> a
unvoidE = either id absurd

-- Isomorphism (assocE, unassocE)
assocE :: Either (Either a b) c -> Either a (Either b c)
assocE (Left (Left a)) = Left a
assocE (Left (Right b)) = Right (Left b)
assocE (Right c) = Right (Right c)

unassocE :: Either a (Either b c) -> Either (Either a b) c
unassocE (Left a) = Left (Left a)
unassocE (Right (Left b)) = Left (Right b)
unassocE (Right (Right c)) = Right c

test1_1, test1_2 :: Cokleisli W Int (Either String ())
test1_1 = rmap Left dump
test1_2 = lmap Left (left' dump)

type B2 = Either (Either Bool ()) ()
type BB = Either (Either Bool Bool) ()
type BBB = Either (Either Bool Bool) Bool

type S2 = Either (Either String ()) ()
type SBB = Either (Either String Bool) Bool

(<++>) :: [a] -> [b] -> [Either a b]
as <++> bs = fmap Left as ++ fmap Right bs

bools = [False, True]

allB2 :: [B2]
allB2 = (bools <++> [()]) <++> [()]

allBB :: [BB]
allBB = (bools <++> bools) <++> [()]

allBBB :: [BBB]
allBBB = (bools <++> bools) <++> bools

test2, test3 :: Cokleisli W (Either (Either Bool b) c) (Either (Either String b) c)
test2 = left' (left' dump)
test3 = dimap assocE unassocE (left' dump)
