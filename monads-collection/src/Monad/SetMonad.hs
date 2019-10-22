{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-|
Module      : SetMonad
Description : Set that is also Monad

This module provides the @Set@ type equipped with @Monad@ instance and most of set
operations provided in the @Data.Set@ module of @containers@ package.

The ability to handling any type is not \"free\". If there is no clue
that @a@ is an instance of @Ord@, a value of @Set a@ is represented by
container that allows duplication of contents.
This sometimes yields serious slowdown, for example:

> -- Inspired by Petr Pudlák <petr.mvd@gmail.com> on Haskell-cafe ML
> -- https://mail.haskell.org/pipermail/haskell-cafe/2013-April/107593.html
>
> var :: Set Int
> var = fromList' [0, 1]
>
> addVars :: Int -> PrimSet Int
> addVars n = runSet (f n) where
>   f 0 = return 0
>   f n = do x <- f (n-1)
>            y <- var
>            return (x+y)

@addVars 100@ will not finish in a realistic time, despite that it does not take a
second if we use @PrimSet@ directly.
To avoid slowdown, you can inform that the type of returned value has Ord instance,
by using 'returnOrd' function.

> addVars' :: Int -> PrimSet Int
> addVars' n = runSet (f n) where
>   f 0 = returnOrd 0
>   f n = do x <- f (n-1)
>            y <- var
>            returnOrd (x+y)

The interface of this module provides no way to observe there are \'duplicated\' element
in the @Set a@. @Foldable@ (and @Traversable@ of course) instance is not
provided because it leaks existence of duplication. For example, what following code
does when there is no @Eq X@ or @Ord X@ instance?

> nums :: Set Int
> nums = fromList [1..10]
> countRange :: (Int -> X) -> Int
> countRange f = Data.Foldable.length (f <$> nums)

-}
module Monad.SetMonad(
  -- * Set with monadic operations
  PrimSet,
  Set(),
  runSet, primitive, repack, returnOrd, forgetOrd,
  -- * Queries
  null, size,
  member, notMember,
  lookupLT, lookupGT,
  lookupLE, lookupGE,
  isSubsetOf, isProperSubsetOf,
  -- * Constructions
  empty,
  singleton,
  insert, delete,
  -- * Binary operations
  union, unions,
  difference, (\\),
  intersection,
  -- * Operations for types which has Ord instance
  -- $ordVariants
  insert',
  union', unions',
  -- * Filters
  filter,
  partition,
  split,
  splitMember,
  -- * Mapping
  map, map',
  mapMonotonic,
  -- * Conversions
  toList, toAscList, toDescList,
  fromList, fromAscList, fromDistinctAscList,
  fromList'
) where

import           Prelude             hiding (filter, map, null)

import qualified Data.Foldable       as F
import           Data.Function       (on)
import           Data.List.NonEmpty  (NonEmpty (..))
import           Data.Semigroup

import qualified Data.Set            (Set)
import qualified Data.Set            as S

import           Control.Applicative hiding (empty)
import qualified Control.Applicative (empty)
import           Control.Monad

-- * Types and primitive operations

-- | Type synonym of 'Data.Set.Set' in "containers"
type PrimSet = Data.Set.Set

-- | Set monad
data Set a where
  Prim :: Ord a => !(PrimSet a) -> Set a
  Cont :: (forall m. Monoid m => (a -> m) -> m) -> Set a

reify :: Ord a => ((a -> PrimSet a) -> PrimSet a) -> PrimSet a
reify f = f S.singleton
{-# INLINE reify #-}

-- | Get concrete @PrimSet a@ by providing @Ord a@ constraint
runSet :: Ord a => Set a -> PrimSet a
runSet (Prim s) = s
runSet (Cont t) = reify t
{-# INLINE runSet #-}

-- | Construct @Set a@ from @PrimSet a@.
primitive :: Ord a => PrimSet a -> Set a
primitive = Prim

-- | > repack = primitive . runSet
repack :: Ord a => Set a -> Set a
repack = primitive . runSet
{-# INLINE repack #-}

-- | Forget that it was @PrimSet a@ and there was the @Ord a@ instance.
forgetOrd :: Set a -> Set a
forgetOrd = map id

{- |
Wrap a single value of @a@ to a singleton set, with witness of
@Ord a@ instance.
You can use @returnOrd@ at the last of do-notation to ensure
constructed @Set a@ is internally @PrimSet a@ and there is no
duplication.

> set1, set2 :: Set Integer
> set1 = do a <- fromList [1..10]
>           b <- fromList [1..10]
>           return (a+b)
> set2 = do a <- fromList [1..10]
>           b <- fromList [1..10]
>           returnOrd (a+b)
>
> f :: Integer -> Integer
> f = {- Very heavy computation here -}
>
> evaluate :: IO ()
> evaluate =
>  do print (fmap f set1) -- f is called 100 times
>     print (fmap f set2) -- f is called 19 times

-}
returnOrd :: Ord a => a -> Set a
returnOrd = singleton'

-- * Queries
null :: Set a -> Bool
null (Prim s) = S.null s
null (Cont t) = getAll $ t (const (All False))

size :: Ord a => Set a -> Int
size = S.size . runSet

member, notMember :: Eq a => a -> Set a -> Bool
member a (Prim s) = S.member a s
member a (Cont t) = getAny (t (\x -> Any (a == x)))
notMember a = not . member a

lookupLT, lookupGT, lookupLE, lookupGE :: Ord a => a -> Set a -> Maybe a
lookupLT a = S.lookupLT a . runSet
lookupGT a = S.lookupGT a . runSet
lookupLE a = S.lookupLE a . runSet
lookupGE a = S.lookupGE a . runSet

isSubsetOf, isProperSubsetOf :: Ord a => Set a -> Set a -> Bool
isSubsetOf s t = S.isSubsetOf (runSet s) (runSet t)
isProperSubsetOf s t = S.isProperSubsetOf (runSet s) (runSet t)

-- * Construction
empty :: Set a
empty = Cont $ const mempty
{-# INLINE empty #-}

singleton :: a -> Set a
singleton a = Cont $ \k -> k a
{-# INLINE singleton #-}

insert :: a -> Set a -> Set a
insert a (Prim s) = Prim $ S.insert a s
insert a (Cont t) = Cont $ \k -> k a `mappend` t k
{-# INLINABLE insert #-}

delete :: Ord a => a -> Set a -> Set a
delete a s = Prim $ S.delete a (runSet s)
{-# INLINABLE delete #-}

-- * Set operations
union :: Set a -> Set a -> Set a
union (Prim s) (Prim t) = Prim $ S.union s t
union (Prim s) (Cont t) = Prim $ S.union s (reify t)
union (Cont s) (Prim t) = Prim $ S.union (reify s) t
union (Cont s) (Cont t) = Cont $ \k -> s k `mappend` t k
{-# INLINABLE union #-}

unions :: [Set a] -> Set a
unions = F.foldl' union empty
{-# INLINABLE unions #-}

difference, (\\) :: Ord a => Set a -> Set a -> Set a
difference s t = Prim $ S.difference (runSet s) (runSet t)
(\\) = difference
{-# INLINABLE difference #-}
{-# INLINABLE (\\) #-}

intersection :: Ord a => Set a -> Set a -> Set a
intersection s t = Prim $ S.intersection (runSet s) (runSet t)
{-# INLINABLE intersection #-}


-- * Always-repack Set operations

{- $ordVariants

Functions like 'insert\'' or 'difference\'' are variants of their original
apostrophe-less counterpart ('insert', 'difference')
in case you know there is an Ord instance. These may or may not be faster than
original function. Usually \"\'\" versions are faster, because they eliminates
duplications.
But consider this:

> manyData1, manyData2 :: Set Text
> manyData1 = fromList [...]
> manyData2 = fromList [...]
>
> textLengthSet  = runSet $ fmap Text.length (manyData1 `union` manyData2)
> textLengthSet' = runSet $ fmap Text.length (manyData1 `union'` manyData2)

If there are many duplications in @Text@ content, @textLengthSet'@ is faster. But
if there are few duplications in @Text@ but many in its length, @textLengthSet@ is
faster because it maps @Text.length@ over many @Text@ values, then actually build
@PrimSet Int@.

-}

empty' :: Ord a => Set a
empty' = Prim S.empty
{-# INLINE empty' #-}

singleton' :: Ord a => a -> Set a
singleton' = Prim . S.singleton
{-# INLINE singleton' #-}

insert' :: Ord a => a -> Set a -> Set a
insert' a s = Prim $ S.insert a (runSet s)
{-# INLINABLE insert' #-}

union' :: Ord a => Set a -> Set a -> Set a
union' s t = Prim $ S.union (runSet s) (runSet t)
{-# INLINABLE union' #-}

unions' :: Ord a => [Set a] -> Set a
unions' = Prim . S.unions . fmap runSet
{-# INLINABLE unions' #-}

map' :: (Ord b) => (a -> b) -> Set a -> Set b
map' f (Prim s) = Prim $ S.map f s
map' f (Cont t) = Prim $ t (S.singleton . f)

-- * Filtering
filter :: (a -> Bool) -> Set a -> Set a
filter p (Prim s) = Prim $ S.filter p s
filter p (Cont t) = Cont $ \k -> t (\x -> if p x then k x else mempty)

partition :: (a -> Bool) -> Set a -> (Set a, Set a)
partition p (Prim s) = let (s1, s2) = S.partition p s
                       in (Prim s1, Prim s2)
partition p s = (filter p s, filter (not.p) s)

split :: Ord a => a -> Set a -> (Set a, Set a)
split a s = let (s1, s2) = S.split a (runSet s)
            in (Prim s1, Prim s2)

splitMember :: Ord a => a -> Set a -> (Set a, Bool, Set a)
splitMember a s =
  let (s1, mem, s2) = S.splitMember a (runSet s)
  in (Prim s1, mem, Prim s2)

-- * Mapping
map :: (a -> b) -> Set a -> Set b
map f (Prim s) = Cont $ \k -> foldMap (k . f) s
map f (Cont t) = Cont $ \k -> t (k . f)

mapMonotonic :: (Ord b) => (a -> b) -> Set a -> Set b
mapMonotonic f (Prim s) = Prim $ S.mapMonotonic f s
mapMonotonic f (Cont t) = Prim $ t (S.singleton . f)

-- * Conversion from/to list
toList, toAscList, toDescList :: Ord a => Set a -> [a]
toList = S.toList . runSet
toAscList = S.toAscList . runSet
toDescList = S.toDescList . runSet

fromList :: [a] -> Set a
fromList [] = empty
fromList xs = Cont $ \k -> F.foldMap k xs

fromList', fromAscList, fromDistinctAscList :: Ord a => [a] -> Set a
fromList' = Prim . S.fromList
fromAscList = Prim . S.fromAscList
fromDistinctAscList = Prim . S.fromDistinctAscList

-- Instances
instance Functor Set where
  fmap = map
  {-# INLINABLE fmap #-}
  a <$ bs = if null bs then empty else singleton a

instance Applicative Set where
  pure = singleton
  {-# INLINABLE pure #-}
  fs <*> as = fs >>= \f -> f <$> as 
  {-# INLINABLE (<*>) #-}
  Prim s <* bs = if null bs then empty' else Prim s
  Cont t <* bs = if null bs then empty else Cont t
  {-# INLINABLE (<*) #-}
  (*>) = flip (<*)
  {-# INLINABLE (*>) #-}

instance Monad Set where
  return = singleton
  {-# INLINABLE return #-}
  as >>= f = case as of
    Prim s -> foldMap f s
    Cont t -> t f
  {-# INLINABLE (>>=) #-}
  (>>) = (*>)
  {-# INLINABLE (>>) #-}

instance Alternative Set where
  empty = empty
  {-# INLINABLE empty #-}
  (<|>) = union
  {-# INLINABLE (<|>) #-}

instance MonadPlus Set where
  mzero = empty
  {-# INLINABLE mzero #-}
  mplus = union
  {-# INLINABLE mplus #-}

instance Semigroup (Set a) where
  (<>) = union
  {-# INLINABLE (<>) #-}
  sconcat (s :| ss) = unions (s:ss)
  {-# INLINABLE sconcat #-}
  stimes = stimesIdempotentMonoid
  {-# INLINEABLE stimes #-}

instance Monoid (Set a) where
  mempty = empty
  {-# INLINABLE mempty #-}

instance Ord a => Eq (Set a) where
  (==) = (==) `on` runSet

instance Ord a => Ord (Set a) where
  compare = compare `on` runSet

instance (Ord a, Show a) => Show (Set a) where
  show = show . runSet
