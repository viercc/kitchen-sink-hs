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

### Readerモナド

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

