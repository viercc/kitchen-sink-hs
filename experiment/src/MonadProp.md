# 多項式モナドの性質

## 定義

### 有限な型と離散的な型

`Nat` を自然数の型とする。`[0], [1], ..., [m], ...`を、それぞれ
`m` 未満の自然数からなる型とする。

型 `X` が_有限である_とは、ある自然数`m`に対して単射 `f :: X -> [m]` を持つことである。

型 `X` に対して、単射 `f :: X -> [m]` をもつような最小の `m` を `X` の_大きさ_とよび、
`|X|` と表記することにする。

Remark. 大きさ `m` を持つ型は、濃度 `m` をもつ有限集合とみなすことができる。
Remark. 型の大きさは同型で保たれる。

Example:

* `()` は大きさ `|()| = 1` をもつ有限な型である。
* `Bool` は大きさ `|Bool| = 1` をもつ有限な型である。
* `[m]` は大きさ `m` をもつ有限な型である。
* `Void` は大きさ `|Void| = 0` をもつ有限な型である。
* `Nat` は有限な型ではない。
* `A`が有限な型であれば、`Maybe A`は大きさ `|Maybe A| = 1 + |A|` をもつ有限な型である。

### 多項式Functor

多項式Functorとは、ある型 `Con` と、`Con`に依存する有限な型の族 `E :: Con -> Type`を用いて、関手

```haskell
type F x = Σ(i :: Con). (E i -> x)
```

と同型になるようなFunctorである。

* `F ()` は `Con` と同型である。

### `ReaderT A Maybe`の埋め込み定理

`T` をモナドとする。`T` に対してある型 `A` が存在して、以下の2つのモナド準同型が存在するとする。

* モナド `R = Reader A` から `T` へのモナド準同型`r`
* モナド `P = Maybe` から `T` へのモナド準同型`p`

```haskell
r :: R x -> T x
p :: P x -> T x
```

`R ∘ P` は、`ReaderT A Maybe` としてモナドの演算を入れることができる。

```haskell
dist :: P (R x) -> R (P x) -- Maybe (A -> x) -> A -> Maybe x
dist prx a = fmap ($ a) prx

instance Monad (R ∘ P) where
    pure :: x -> R (P x)
    pure x = const (Just x)

    join :: R (P (R (P x))) -> R (P x)
    join = fmap (join @P) . join @R . fmap dist
```

このとき、以下のように定義される`R ∘ P` から `T` への自然変換`rp`は、モナド準同型である。

```haskell
rp :: R (P x) -> T x
rp = join @T . r . fmap p
```

このためにまず、 `dist` による `P` と `R` の順序の入れ替えが、
`r, p` によってモナド `T` にうつしたとき、 `T` のモナド乗法では可換になることをみる。
すなわち、以下の自然変換`pr`を用いて、`rp . dist = pr` が成り立つ。

```haskell
pr :: P (R x) -> T x
pr = join . p . fmap r

-- 証明
rp (dist Nothing)
  = rp (\a -> fmap ($a) Nothing)
  = rp (const Nothing)
  = join $ r (const (p Nothing))
    -- r . const = r . pure @R = pure @T
  = join . pure $ p Nothing
  = p Nothing
  = p . fmap r $ Nothing
  = pr Nothing

rp (dist (Just f))
  = rp (\a -> fmap ($ a) (Just f))
  = join . r . fmap p $ \a -> Just (f a)
  = join . r . fmap p . fmap Just $ f
  = join . r . fmap pure $ f
  = join . fmap pure $ r f
  = r f
pr (Just f)
  = join . p . fmap r $ Just f
  = join . p $ Just (r f)
  = join . pure $ r f
  = r f
```

これを用いてrpがモナド準同型であることを証明する。

```haskell
type RP = R ∘ P
-- preserve pure
rp . pure @RP
  = join . r . fmap p . pure @R . pure @P
  = join . r . pure @R . p . pure @P
  = join . pure . pure
  = pure

-- preserve join
rp . join @RP
  = join . r . fmap p . fmap (join @P) . join @R . fmap dist
  -- Naturality
  = join . fmap (p . join @P) . (r . join @R) . fmap dist
  --             ^^^^^^^^^^^     ^^^^^^^^^^^ p, r are Monad morphisms
  = join . fmap (join . p . fmap p) . (join . r . fmap r) . fmap dist
  -- Reassociate (.)
  = join . fmap join . fmap (p . fmap p) . join . (r . fmap r) . fmap dist
  --                   ^^^^^^^^^^^^^^^^^^^^^^^^ fmap f . join = join . fmap (fmap f)
  = join . fmap join . join . fmap (fmap (p . fmap p)) . r . fmap r . fmap dist
  --                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ :: ∀x. R (R (P (P x))) -> T (T (T (T x)))
  -- Reorder natural transformations
  = (join . fmap join . join) . (fmap . fmap . fmap) p . r . fmap (fmap p . r . dist)
  -- ^^^^^^^^^^^^^^^^^^^^^^^ Apply monad law twice
  = (join . join . fmap join) . (fmap . fmap . fmap) p . r . fmap (fmap p . r . dist)
  --               ^^^^^^^^^---------------------------vvvv
  = (join . join) . (fmap . fmap . fmap) p . r . fmap (join . fmap p . r . dist)
  -- join . fmap p . r . dist = pr . dist = rp = join . p . fmap r
  = (join . join) . (fmap . fmap . fmap) p . r . fmap (join . p . fmap r)
  = (join . join . fmap join) . (fmap . fmap . fmap) p . (fmap . fmap) r . fmap p . r
  = (join . fmap join . join) . fmap (fmap (fmap p . r)) . fmap p . r
  = join . fmap join . fmap (fmap p . r) . join . fmap p . r
  = join . fmap pr . pr
```

`r` と `p` がともに単射である状況を考える。（TODO:自然変換が単射⇔各成分が単射）

> `r` と `p` が単射であれば `rp` も単射である

Remark. このとき `pure = p . Just` も単射であり、任意の `x` に対して `pure x /= p Nothing` である。

以下、証明のために次の`reconstruct`という関数を考える。

```haskell
onlyWhen :: (A -> Bool) -> R x -> R (P x)
onlyWhen cond x = \i -> if cond i then Just (x i) else Nothing

reconstruct :: (A -> Bool) -> R x -> T x
reconstruct cond x = join . rp $ \i ->
  if cond i then Just (rp (onlyWhen cond x)) else Just (rp (onlyWhen (not . cond) x))
```

ここで、`rp`がモナド準同型であったことをもとに`reconstruct`を計算すると、

```haskell
reconstruct cond x
  = join . rp $ \i ->
      if cond i then Just (rp (onlyWhen cond x)) else Just (rp (onlyWhen (not . cond) x))
  = join . rp . fmap @RP rp $ \i ->
      if cond i then Just (onlyWhen cond x) else Just (onlyWhen (not . cond) x)
    -- rpはモナド準同型
  = rp . join @RP $ \i ->
      if cond i then Just (onlyWhen cond x) else Just (onlyWhen (not . cond) x)
  = rp $ \i ->
      if cond i then onlyWhen cond x i else onlyWhen (not . cond) i x
  = rp $ \i ->
      if cond i then Just (x i) else Just (x i)
  = rp $ \i -> Just (x i)
  = r x
```

である。特に、`r`は単射であったことから、
`reconstruct cond x`はどの点`i :: A`においても`x i`に依存することに注意する。

`x`が`Void`のように空な型であるとき、`R (P x) = A -> Maybe x` は`const Nothing`以外の値をとれず、
`()`と同型である。このとき、`rp :: R (P x) -> T x`は自明に単射である。
そのため、以下`x`は空でないと仮定する。

Fact1. `rp y = p Nothing` ならば `y = const Nothing`

`x`が空でなければ、`y :: R (P x)` は、ある `x, cond` によって `y = onlyWhen cond x` と書ける。
もし `rp y = p Nothing` であれば、それはどの `i :: A` についても `x i` に依存していないため、
`reconstruct cond x`がすべての `i :: A` について `x i` に依存するために、
任意の `i` に対して `onlyWhen (not . cond) x i = Just (x i)`でなければならない。
これはすなわち、`not . cond = const True`であり、
`y = onlyWhen cond x = onlyWhen (const False) x = const Nothing`を意味する。

Fact2. `()`における自然変換`rp`の成分 `rp :: R (P ()) -> T ()` は単射である。

次の関数 `intersection` を考える。

```haskell
(>>) :: T a -> T b -> T b
t >> u = join $ fmap (const u) t

intersection :: R (P ()) -> R (P ()) -> T ()
intersection x y = rp x >> rp y
```

`intersection x y`は`rp z`の形に書くことができる。

```haskell
intersection x y
  = join . fmap (const (rp y)) $ rp x
  = join . fmap rp . fmap (const y) . rp $ x
  = join . fmap rp . rp $ fmap (const y) x
  = rp . join @RP $ fmap (const y) x
  = rp $ \i -> x i >>= const (y i)
  = rp $ \i -> andP (x i) (y i)
    where andP (Just ()) (Just ()) = Just ()
          andP _         _         = Nothing
```

ここで、`intersection x1 = intersection x2`が成り立っていたとする。
すなわち、任意の `y`に対して`intersection x1 y = intersection x2 y`である。

ここで、`y1, y2`を以下のようにとる。

```haskell
y1, y2 :: R (P ())
y1 i = x1 i `subP` x2 i
y2 i = x2 i `subP` x2 i

subP :: P () -> P () -> P ()
subP (Just ()) Nothing = Just ()
subP _         _       = Nothing
```

いま、`y1, y2`の構成から

* `intersection x1 y2 = p Nothing`
* `intersection x2 y1 = p Nothing`

である。仮定より

* `intersection x1 y1 = p Nothing`
* `intersection x2 y2 = p Nothing`

でもあり、更に `intersection x y = p Nothing`が成り立つのは、
任意の`i`に対して`x i == Nothing || y i == Nothing`が成り立つときに限る (∵Fact1) から、

* 任意の`i`に対して `x1 i == Nothing || x2 i /= Nothing` が成り立つ
* 任意の`i`に対して `x2 i == Nothing || x1 i /= Nothing` が成り立つ

よって、任意の`i`に対して `x1 i == x2 i` である。
すなわち、`intersection`は`x`単独の関数として単射である。
これは `rp :: R (P ()) -> T ()` も単射でなければ不可能である。

Fact3. 任意の`a`について`rp :: R (P a) -> T a`は単射である。

`rp y1 = rp y2`が成り立つ`y1, y2 :: R (P a)`について、`y1 = y2`を示す。

Fact1を示すときに述べたように、

* `x1, cond1`が存在して`y1 = onlyWhen cond1 x1`
* `x2, cond2`が存在して`y2 = onlyWhen cond2 x2`

とできる。更に、`a`は空でないので、ある`x0 :: a`をとって、

* `cond1 i == False`のとき`x1 i = x0`
* `cond2 i == False`のとき`x2 i = x0`

となるように`x1, x2`をとることができる。

また、Fact2から、`rp y1 = rp y2`であれば`cond1 = cond2`となるから、`cond1 = cond2 = cond`とできる。
このとき、

```haskell
r x1
  = reconstruct cond x1
  = join . rp $ \i ->
      if cond i then Just (rp (onlyWhen cond x1)) else Just (rp (onlyWhen (not . cond) x1))
  = join . rp $ \i ->
      if cond i then Just (rp y1) else Just (rp (onlyWhen (not . cond) (const x0)))
    -- 仮定より rp y1 = rp y2
  = join . rp $ \i ->
      if cond i then Just (rp y2) else Just (rp (onlyWhen (not . cond) (const x0)))
  = join . rp $ \i ->
      if cond i then Just (rp (onlyWhen cond x2)) else Just (rp (onlyWhen (not . cond) x2))
  = reconstruct cond x2
  = r x2
```

より`x1 = x2`、したがって`y1 = y2`である。
よって`rp`が単射であることが示された。