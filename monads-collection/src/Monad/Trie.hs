{-# LANGUAGE DeriveTraversable #-}

module Monad.Trie where

import Control.Applicative hiding (empty)
import Control.Monad (ap)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import MonadLaws

data Trie c a = Trie (Maybe a) (Map c (Trie c a))
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show c, Show a) => Show (Trie c a) where
  showsPrec p t = showParen (p > 10) $ showString "fromList " . showsPrec 11 (toAscList t)

-- * Construction

empty :: Trie c a
empty = Trie Nothing Map.empty

just :: a -> Trie c a
just a = Trie (Just a) Map.empty

singleton :: [c] -> a -> Trie c a
singleton cs a = foldr consTrie (just a) cs
  where
    consTrie c t = Trie Nothing (Map.singleton c t)

unionWith :: (Ord c) => (a -> a -> a) -> Trie c a -> Trie c a -> Trie c a
unionWith op (Trie mA edgesA) (Trie mB edgesB) = Trie (unionMaybe op mA mB) (Map.unionWith (unionWith op) edgesA edgesB)

unionMaybe :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
unionMaybe _ Nothing mb = mb
unionMaybe _ ma Nothing = ma
unionMaybe op (Just a) (Just b) = Just (op a b)

insert :: Ord c => [c] -> a -> Trie c a -> Trie c a
insert cs a = unionWith const (singleton cs a)

fromList :: Ord c => [([c], a)] -> Trie c a
fromList = foldl' (\t (cs, a) -> insert cs a t) empty

-- * Query

foldrWithKey :: ([c] -> a -> r -> r) -> r -> Trie c a -> r
foldrWithKey f z (Trie ma e) =
  case ma of
    Nothing -> r
    Just a -> f [] a r
  where
    r = Map.foldrWithKey nextChar z e
    nextChar c subTrie s = foldrWithKey (f . (c :)) s subTrie

toAscList :: Trie c a -> [([c], a)]
toAscList = foldrWithKey (\cs a r -> (cs, a) : r) []

----

instance Ord c => Applicative (Trie c) where
  pure = just
  (<*>) = ap

instance Ord c => Monad (Trie c) where
  Trie ma edges >>= k = case ma of
    Nothing -> Trie Nothing (fmap (>>= k) edges)
    Just a -> glue (k a) (fmap (>>= k) edges)

glue :: Trie c a -> Map c (Trie c a) -> Trie c a
glue t shoot
  | Map.null shoot = t
  | otherwise = case t of
      Trie ma edges
        | Map.null edges -> Trie ma shoot
        | otherwise -> Trie ma (fmap (`glue` shoot) edges)

--

enumTrie :: Enum1 (Trie Char)
enumTrie ma = t0 <|> t1 <|> tnull <|> tbranch <|> t2
  where
    t0 = just <$> ma
    t1 = singleton <$> (pure "a" <|> pure "b") <*> ma
    t2 = singleton "aa" <$> ma
    tnull = pure $ Trie Nothing (Map.singleton 'a' empty)
    tbranch = tbranch' <$> ma <*> ma
    tbranch' a0 a1 = fromList [("a", a0), ("ab", a1)]