module Monad.Searchable where

-- | Searchable set
newtype Set a = Set {find :: (a -> Bool) -> a}

search :: Set a -> (a -> Bool) -> Maybe a
search xs p = let x = find xs p in if p x then Just x else Nothing

forsome, forevery :: Set a -> (a -> Bool) -> Bool
forsome xs p = p (find xs p)
forevery xs p = not $ forsome xs (not . p)

member :: (Eq a) => a -> Set a -> Bool
member x xs = forsome xs (== x)

singleton :: a -> Set a
singleton x = Set (const x)

bit :: Set Bool
bit = Set (\p -> p True)

blackhole :: Set a
blackhole = Set (error "Tried to test blackhole!")

doubleton :: a -> a -> Set a
doubleton x y = Set (\p -> if p x then x else y)

bigUnion :: Set (Set a) -> Set a
bigUnion xss = Set (\p -> find (find xss (\xs -> forsome xs p)) p)

union :: Set a -> Set a -> Set a
union xs ys = bigUnion (doubleton xs ys)

filter :: (a -> Bool) -> Set a -> Set a
filter p xs = Set $ \q -> find xs (\x -> q x && p x)

prod :: Set a -> Set b -> Set (a, b)
prod as bs = Set $ \p ->
  let a = find as (\a' -> forsome bs (\b -> p (a', b)))
   in (a, find bs (\b -> p (a, b)))

sum :: Set a -> Set b -> Set (Either a b)
sum as bs = union (fmap Left as) (fmap Right bs)

intersection :: (Eq a) => Set a -> Set a -> Set a
intersection xs ys = Monad.Searchable.filter (`member` ys) xs

instance Functor Set where
  fmap f xs = Set $ \q -> f (find xs (q . f))

instance Applicative Set where
  pure = singleton
  fs <*> xs = fmap (uncurry ($)) $ prod fs xs

instance Monad Set where
  xs >>= f = bigUnion (fmap f xs)
