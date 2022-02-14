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

Remark. このとき `pure = p . Just` も単射である。`Just :: a -> Maybe a` は定義から単射である。

証明のため、以下の `split` と `repair` という関数を考える。

```haskell
split :: R (Bool, x) -> (R (P x), R (P x))
split rbx = (fmap getLeft rbx, fmap getRight rbx)

getLeft :: Either x y -> Maybe x
getLeft = either Just (const Nothing)

getRight :: Either x y -> Maybe y
getRight = either (const Nothing) Just

repair :: (T x, T y) -> (A -> Bool) -> T (Either x y)
repair (tx, ty) cond = join . r $ \i -> if cond i then fmap Left tx else fmap Right ty
```

次の関数`rezip`は、（1変数関数として）単射であることを示す。

```haskell
rezip :: R (Either x y) -> (A -> Bool) -> T (Either x y)
rezip = repair . (rp *** rp) . split
```

`rezip`を既知の`rp`の性質を使って計算すると、
以下のようになる。

```haskell
xy :: R (Either x y)
cond :: A -> Bool

rezip xy cond
  = repair ((rp *** rp) (split xy)) cond
  = repair (rp (fmap getLeft xy), rp (fmap getRight xy)) cond
  = join . r $ \i ->
      if cond i then fmap Left  (rp (fmap getLeft xy))
                else fmap Right (rp (fmap getRight xy))
  = join . r . fmap rp $ \i ->
      if cond i then (fmap (fmap Left)  . fmap getLeft) xy
                else (fmap (fmap Right) . fmap getRight) xy
  = join . r . fmap (join . r . fmap p) $ \i ->
      if cond i then fmap (fmap Left  . getLeft) xy
                else fmap (fmap Right . getRight) xy
    -- ここで、`$` の手前は
          join . r . fmap (join . r . fmap p)
        = join . fmap join . r . fmap r . fmap (fmap p)
        = join . join . r . fmap r . fmap (fmap p)
        = join . r . join @R . fmap (fmap p)
        = join . r . fmap p . join @R
    -- であるから
  = join . r . fmap p . join @R $ \i -> 
      if cond i then fmap (fmap Left  . getLeft) xy
                else fmap (fmap Right . getRight) xy
  = rp $ \i -> 
      if cond i then (fmap Left  . getLeft) (xy i)
                else (fmap Right . getRight) (xy i)
  = rp $ \i ->
      if cond i
        then if isLeft (xy i)
                then Just (xy i)
                else Nothing
        else if isRight (xy i)
                then Just (xy i)
                else Nothing
  = rp $ \i -> if cond i == isLeft (xy i) then Just (xy i) else Nothing
```

この結果より、以下の2点がいえる。

* `cond = isLeft . xy` ⇔ `rezip xy cond = r xy`

  なぜならば、`cond = isLeft . xy`であるとき、
  
  ```haskell
  rezip xy cond 
    = rp $ \i -> if cond i == isLeft (xy i) then Just (xy i) else Nothing
    = rp $ \i -> Just (xy i)
    = join . r . fmap p . fmap Just $ \i -> xy i
    = join . fmap pure . r $ xy
    = r xy
  ```
  
  また、`cond /= isLeft . xy` であるとき、`cond i /= isLeft (xy i)` であるような `i` が存在する。
  `r xy :: T (Either x y)` は、`r`の単射性から `xy i :: Either x y` の値に依存するが、
  `rezip xy cond` においては `xy i` の値に依存せず、したがって `xy' /= r xy` である。

* `cond = not . isLeft . xy` ⇔ `rezip xy cond = p Nothing`

  ⇒は同様に計算するだけでわかる。⇐の対偶を示すため、`cond /= not . isLeft . xy`であったとする。
  
  前述した計算結果から、`rezip xy cond`は、適当な`u :: R (P (Either x y))`によって`rp u`と書ける。
  ここで、`v :: R (P z)`であって、`(u, v) = split uv`であるような`v`と`uv`を考えると、

  ```haskell
  rezip uv cond'
    = repair (rp u, rp v) cond'
    = repair (rezip xy cond, rp v) cond'
  ```
  
  である。`u` は、`cond i == isLeft (xy i)`を満たす `i` において `u i = Just (xy i)`となっているが、
  `rezip xy cond = p Nothing`ならば`rezip uv cond'` は `xy i` に依存できないことがわかる。
  しかし、`cond' = isLeft uv'`とすれば、
  前節の通り `rezip uv cond' = r uv`なのであるから、`uv i = Left (xy i)`には明らかに依存する。
  仮定から`cond i == isLeft (xy i)`を満たす `i` は常に存在するので、これは不合理である。したがって
  `rezip xy cond = p Nothing`であってはならない。

よって、任意の`xy1, xy2 :: R (Either x y)` かつ `xy1 /= xy2`に対して、

* `cond = isLeft . xy1 = isLeft . xy2` であるとき、 `rezip xy1 cond = r xy1 /= r xy2 = rezip xy2 cond`
* `isLeft . xy1 /= isLeft . xy2` であるとき、 `rezip xy1 (not . isLeft . xy1) = p Nothing /= rezip xy2 (not . isLeft . xy1)`

であるから、`rezip`は単射である。

さて、以下の`rezip`は単射なのであったが、`split`が単射であることから
`rp *** rp`も単射でなければならない。

```haskell
rezip :: R (Either x y) -> (A -> Bool) -> T (Either x y)
rezip = repair . (rp *** rp) . split
```

一般論として、`f *** g`が単射であることと、`f`と`g`がいずれも単射であることは同値である。
従って、`rp`も単射でなければならない。
