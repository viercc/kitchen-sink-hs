# It must be `return x = [x]` for any possible `Monad []` instance

This is inspired by [the original proof](https://qiita.com/1to100pen/items/4c0909d07174203c1f8b) written by
@1to100pen([twitter](https://twitter.com/1to100pen)). Large portion of the arguments are same to the original,
but many notational changes might make it look less alike.

I've reused the notations from my related, [older proof](https://viercc.github.io/blog/posts/2019-12-16-fixed-proof-for-monads-more.html) about some polynomial functors lacking any "singleton" value can't have a lawful `Monad` instance.

## Statement

For any possible `Monad` instance on the list functor `[]`,
the only possible choice of `return` is `\x -> [x]`.

## Preliminary

* Any function `f` with type `∀a. a -> [a]` is characterized
  by the length of `f x :: [a]`, a constant which doesn't depend on
  neither type nor value of `x`.

Suppose the length of `return ()` be `n ∈ ℕ∪{∞}`.
The statement is the only choice of `n` is `n=1`.


Let n be the length of `return ()` and `us` be a list of length n where
each element is its own index. In other words, `us = [0,1,2, ..., ... n-1]`
(or `us = [0,1,...]` for `n=∞`.)

I'll use the following definitions for conveniences:

```haskell
u :: (Nat -> x) -> [x]
u f = f <$> us

sw :: Nat -> x -> x -> [x]
sw i x y = u $ \j -> if i == j then x else y
```

I'll use these facts without saying so.

* `join [] = []`

* `return a = u (const a) = sw i a a`

## Proof

* **Fact1**: n > 0.

  Do proof by contradiction.
  Suppose n=0, which means `return = const []`. Then
  ```haskell
  join . return = join . const [] = const (join []) = const []
  ```
  But by the monad laws `join . return = id`. Contradiction.

* **Fact2**: Any n×n-shaped list of lists `xss` can be represented as `xss = u $ \i -> u $ \j -> f i j`,
  using some function `f :: Nat -> Nat -> a`. `join` on `xss` is taking the diagonal elements i.e.
  `join xss = u $ \i -> f i i`.
  
  Let `uss :: [[Nat]]` be a n\*n-shaped list of lists of "coordinates" defined as below.
  ```haskell
  uss = fmap (\i -> fmap (\j -> (i,j)) us) us
  ```
  Because `join xss = join (fmap (fmap (uncurry f)) uss) = fmap (uncurry f) (join uss)`, it suffices to show:
  ```haskell
  join uss = fmap (\i -> (i,i)) us = u $ \i -> (i,i)
  ```
    
  Using the monad laws, `join uss` must satisfy the following equations
  ```haskell
  fst <$> join uss
    = join $ fmap (fmap fst) uss
    = join $ fmap (\i -> fmap (\j -> fst (i,j)) us) us
    = join $ fmap (\i -> fmap (const i) us) us
    = join $ fmap (\i -> return i) us
    = join $ fmap return us
    = us
  snd <$> join uss
    = join $ fmap (fmap snd) uss
    = join $ fmap (\i -> fmap (\j -> snd (i,j)) us) us
    = join $ fmap (\i -> fmap (\j -> j) us) us
    = join $ fmap (\i -> us) us
    = join $ return us
    = us
  ```
  And the only possible value of `join uss` satisfying them is `(\i -> (i,i)) <$> us`.

As a corollary, the following holds (join-sw-sw):

```haskell
join $ sw i (sw i xx xy) (sw i yx yy) = sw i xx yy
```

Think about the properties of the following functions:

```haskell
at :: Nat -> a -> [a]
at i a = join $ sw i (return a) []

hole :: Nat -> [a] -> [a]
hole i as = join $ sw i [] as
```

* **Fact3**: `length (at i x) > 0`
  
  Consider the following value:
  ```haskell
  sweep :: [[Nat]]
  sweep = u $ \i -> at i i
  ```
  By the monad laws, `join sweep = us` can be shown.
  For any `i` such that `0 <= i < n`, it shouldn't be `at i x = []`,
  as there must be one or more elements of value `i` in `at i i`
  to have `i` in `join sweep`.
  
  ```haskell
  join sweep
    = join $ u $ \i -> at i i
    = join $ u $ \i -> join $ sw i (return i) []
    = join . fmap join $ u $ \i -> sw i (return i) []
    = join . join $ u $ \i -> u $ \j ->
        if i == j then return i else []
    -- (Fact2)
    = join $ u $ \i ->
        if i == i then return i else []
    = join $ u $ \i -> return i
    = join . fmap return $ u id
    = us
  ```

Let's prepare several lemma about `at`.

* **join-at**: `join (at i xs) = join (sw i xs [])`

  ```haskell
  join $ at i xs
    = join . join $ sw i (return xs) []
    = join . fmap join $ sw i (return xs) []
    = join $ sw i (join $ return xs) (join [])
    = join $ sw i xs []
  ```
  
* **join-at-u**: `join (at i (u f)) = at i (f i)`

  First show `join (at i us) = at i i`.

  ```haskell
  join $ at i us
    -- (join-at)
    = join $ sw i us []
    = join $ sw i (join $ fmap return us) (join $ return [])
    = join . fmap join $ sw i (fmap return us) (return [])
    = join . join $ sw i (fmap return us) (return [])
    = join . join $ u $ \j -> u $ \k ->
        if i == j then return k else []
    -- (Fact2)
    = join $ u $ \j ->
        if i == j then return j else []
    = join $ u $ \j ->
        if i == j then return i else []
    = join $ sw i (return i) []
    = at i i
  ```
  
  Then the lemma follows from naturality.
  
  ```haskell
  join $ at i (u f)
    = join $ at i (fmap f us)
    = join . fmap (fmap f) $ at i us
    = fmap f $ join $ at i us
    = fmap f $ at i i
    = at i (f i)
  ```
  
* **join-u-at**: `join (u (at i)) = at i i`

  ```haskell
  join $ u $ at i
    = join $ u $ \j -> at i j
    = join $ u $ \j -> join $ sw i (return j) []
    = join . fmap join $ u $ \j -> sw i (return j) []
    = join . join $ u $ \j -> u $ \k ->
        if i == k then return j else []
    -- (Fact2)
    = join $ u $ \j ->
        if i == j then return j else []
    = join $ u $ \j ->
        if i == j then return i else []
    = at i i
  ```

* **(hole-at)**: `hole i (at i x) = []`
  
  ```haskell
  hole i (at i x)
    = join $ sw i [] (at i x)
    = join $ sw i (join $ return []) (join $ sw i (return x) [])
    = join . fmap join $ sw i (return []) (sw i (return x) [])
    = join . join $ sw i (return []) (sw i (return x) [])
    -- (join-sw-sw)
    = join $ sw i [] []
    = []
  ```

* **Fact4**: If `length (at i x) = length (at j x)`, then `i = j`.

  Because `at i :: a -> [a]` for any `i`,
  the only difference between `at i x` and `at j x` is its length.
  When the lengths of `at i x` and `at j x` are equal, which implies `at i = at j`,
  `at i i = join (u (at i)) = join (u (at j)) = at j j` by (join-u-at).
  By Fact3, both `at i i` and `at j j` are not empty.
  Thus `i = j` must hold.

* **Fact5**: `length (at i x) = 1` for any `i`.
  
  Suppose `length (at i x) >= 2`. Then there should be
  a function `con :: a -> a -> [a]` where `con x x = at i x`
  and `con x y` contains both `x` and `y` as its elements.
  
  By `con x x = at i x` and parametricity,
  `hole i (con x y) = []` follows from (hole-at). Let's name this equation (hole-con).
  Then the following (join-at-con) holds:
  
  ```haskell
  join $ at i (con x y)
    -- (join-at)
    = join $ sw i (con x y) []
    -- (hole-con)
    = join $ sw i (con x y) (hole i (con x y))
    = join $ sw i (join . return $ con x y) (join $ sw i [] (con x y))
    = join . fmap join $ sw i (return (con x y)) (sw i [] (con x y))
    = join . join $ sw i (return (con x y)) (sw i [] (con x y))
    -- (join-sw-sw)
    = join $ sw i (con x y) (con x y)
    = con x y
  ```
  
  Consider the following function:
  ```haskell
  extra :: Nat -> a -> a -> a -> [a]
  extra i x y z = join $ sw i (con x y) (return z)
  ```
  
  Using `con x x = at i x`, `extra i x x z` can be calculated as follows:
  ```haskell
  extra i x x z
    = join $ sw i (con x x) (return z)
    = join $ sw i (at i x) (return z)
    = join $ sw i (join $ sw i (return x) []) (join . return $ return z)
    = join . fmap join $ sw i (sw i (return x) []) (return $ return z)
    = join . join $ sw i (sw i (return x) []) (return $ return z)
    -- (join-sw-sw)
    = join $ sw i (return x) (return z)
    = sw i x z
  ```
  By parametricity, `extra i x y z` depends on `z` and either `x` or `y`, exclusive.
  
  But by calculating in another way,
  ```haskell
  join $ at i (extra i x y z)
    = join $ at i $ join $ sw i (con x y) (return z)
    = join . fmap join $ at i $ sw i (con x y) (return z)
    = join . join $ at i $ sw i (con x y) (return z)
    = join . join $ at i $ u $ \j -> if i == j then con x y else return z
    -- (join-at-u)
    = join $ at i (con x y)
    -- (join-at-con)
    = con x y
  ```
  Which by definition depends on both `x` and `y`, leading contradiction.
  
  Thus the hypothesis, `length (at i x) >= 2`, was false. Considering Fact3 (`length (at i x) > 0`),
  the only possible length of `at i x` is 1.

Fact1 states `n > 0`.
Fact4 states the length of `at i x` is distinct for each different `i`, `0 <= i < n`.
Fact5 states the length of `at i x` is always 1.
To satisfy both, there can't be two different `i,j` such that `0 <= i,j < n`.
Therefore, `n = 1`.

