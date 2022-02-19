# On `FreeT' m` being lawful `FMonad`

## Definitions

### FFunctor and FMonad

```haskell
type (~>) f g = forall a. f a -> g a

{-| Functor on 'Functor's

FFunctor laws:
>  ffmap id = id
>  ffmap f . ffmap g = ffmap (f . g)

-}
class (forall g. Functor g => Functor (ff g)) => FFunctor ff where
    ffmap :: (Functor g, Functor h) => (g ~> h) -> (ff g ~> ff h)
```

```haskell
{-| Monad on 'Functor's

FMonad laws:

[fpure is natural in g]

    ∀(n :: g ~> h). ffmap n . fpure = fpure . n

[fjoin is natural in g]

    ∀(n :: g ~> h). ffmap n . fjoin = fjoin . ffmap (ffmap n)

[Left unit]

    fjoin . fpure = id

[Right unit]

    fjoin . fmap fpure = id

[Associativity]

    fjoin . fjoin = fjoin . ffmap fjoin

-}
class FFunctor ff => FMonad ff where
    fpure :: (Functor g) => g ~> ff g
    fjoin :: (Functor g) => ff (ff g) ~> ff g
```

### FreeT'

[FreeT'](./FMonad.hs#L382), cf. [FreeT](https://hackage.haskell.org/package/free-5.1.3/docs/Control-Monad-Trans-Free.html#t:FreeT)

```haskell
-- FreeT' is (Flip FreeT)
newtype FreeT f m b = FreeT { runFreeT :: m (FreeF f b (FreeT f m b)) }

newtype FreeT' m f b = FreeT' { unFreeT' :: FreeT f m b }
    deriving (Applicative, Monad) via (FreeT f m)

-- Sadly, Functor (FreeT m f) uses liftM instead of fmap,
-- meaning (Monad m, Functor f) => Functor (FreeT f m).
-- Maybe that was for backward compatibility,
-- but I want (Functor m, Functor f) => ...
fmapFreeT_ :: (Functor f, Functor m) => (a -> b) -> FreeT f m a -> FreeT f m b
fmapFreeT_ f = FreeT . fmap (bimap f (fmapFreeT_ f)) . runFreeT

ffmapFreeF :: forall f g a. (f ~> g) -> FreeF f a ~> FreeF g a
ffmapFreeF _  (Pure a)  = Pure a
ffmapFreeF fg (Free fb) = Free (fg fb)

-- Same!
transFreeT_ :: forall f g m. (Functor g, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
transFreeT_ fg =
  let go = FreeT . fmap (fmap go . ffmapFreeF fg) . runFreeT in go

instance (Functor m, Functor f) => Functor (FreeT' m f) where
    fmap f (FreeT' mx) = FreeT' (fmapFreeT_ f mx)

instance Functor m => FFunctor (FreeT' m) where
    ffmap f = FreeT' . transFreeT_ f . unFreeT'

instance Monad m => FMonad (FreeT' m) where
    fpure :: forall g. Functor g => g ~> FreeT' m g
    fpure gx = FreeT' (liftF gx)
    
    fjoin :: forall g. Functor g => FreeT' m (FreeT' m g) ~> FreeT' m g
    fjoin =  FreeT' . fjoin_ . transFreeT_ unFreeT' . unFreeT'
      where
        fjoin_ :: FreeT (FreeT g m) m ~> FreeT g m
        fjoin_ = retractT

-- Copy-pasted from "free"
retractT :: (MonadTrans t, Monad (t m), Monad m) => FreeT (t m) m a -> t m a
retractT (FreeT m) = do
  val <- lift m
  case val of
    Pure x -> return x
    Free y -> y >>= retractT
```

### Monad morphism

Natural transformation between `Functor`s `nt :: f ~> g` is a
monad morphism iff

* `nt . return @f = return @g`
* `nt . join @f = join @g . fmap nt . nt`

### Definitions for proof

``` haskell
inr :: (Monad m) => m ~> FreeT f m
inr = lift
inr mx = FreeT $ fmap Pure mx

inl :: (Functor f, Monad m) => f ~> FreeT f m
inl = liftF
inl gx = FreeT . return @m . Free . fmap (return @(FreeT m f)) $ mx
```

## Proof 

### Universal Property

**Statement:** Let `m,n` be a `Monad`, `f` be a `Functor`.
For all natural transformation `nt1 :: f ~> n` and monad morphism `nt2 :: m ~> n`, there exists
a unique monad morphism `nt :: FreeT f m ~> n` with properties

* `nt . inl = nt1`
* `nt . inr = nt2`

**Proof:**

The following `eitherFreeT nt1 nt2` is the monad morphism `FreeT f m ~> n`.

```haskell
eitherFreeT :: (Monad m, Monad n, Functor f) => (f ~> n) -> (m ~> n) -> (FreeT f m ~> n)
eitherFreeT nt1 nt2 = go
  where
    go ma =
      do v <- nt2 (runFreeT ma)
         case v of
           Pure a  -> return a
           Free fm -> nt1 fm >>= go
```

**(1)** It is actually a monad morphism

`go . return = return` is straightforward.

```haskell
go $ return a
  = go (FreeT (return (Pure a)))
  = do v <- nt2 (return (Pure a))
       case v of
         Pure a  -> return a
         Free fm -> nt1 fm >>= go
    -- nt2 . return = return
  = case Pure a of
      Pure a  -> return a
      Free fm -> nt1 fm >>= g0
  = return a
```

`go . join` and `join . fmap go . go` are equal by induction.

```hasekll
join . fmap go . go $ mma
 = go mma >>= go
 = do v <- nt2 $ runFreeT mma
      ma' <- case v of
        Pure ma -> return ma
        Free fm -> nt1 fm >>= go
      go ma'
 = do v <- nt2 $ runFreeT mma
      case v of
        Pure ma -> return ma     >>= go
        Free fm -> nt1 fm >>= go >>= go
 = do v <- nt2 $ runFreeT mma
      case v of
        Pure ma -> go ma
        Free fm -> nt1 fm >>= join . fmap go . go

go $ join mma
  = go . FreeT $ runFreeT mma >>= \v -> case v of
      Pure a  -> runFreeT a
      Free fm -> return (Free (fmap join fm))
  = do v' <- nt2 $ do
         v <- runFreeT mma
         case v of
           Pure ma -> runFreeT ma
           Free fm -> return $ Free (fmap join fm)
       case v' of
         Pure a  -> return a
         Free fm -> nt1 fm >>= go
    -- nt2 is a monad morphism
  = do v <- nt2 mma
       v' <- case v of
         Pure ma -> nt2 $ runFreeT ma
         Free fm -> return $ Free (fmap join fm)
       case v' of
         Pure a  -> return a
         Free fm -> nt1 fm >>= go
  = do v <- nt2 mma
       case v of
         Pure ma -> do
           ---- This part is equal to (go ma) ----
           v' <- nt2 $ runFreeT ma
           case v' of
             Pure a  -> return a
             Free fm -> nt1 fm >>= go
           ---------------------------------------
         Free fm -> nt1 (fmap join fm) >>= go
  = do v <- nt2 mma
       case v of
         Pure ma -> go ma
         Free fm -> nt1 fm >>= go . join
```

**(2)** Composing with injections gets original arrows back

```haskell
go $ inl fa
 = do v <- nt2 . runFreeT $ FreeT . return . Free $ fmap return fa
      case v of
        Pure a  -> return a
        Free fm -> nt1 fm >>= go
 = case Free (fmap return fa) of
     Pure a  -> return a
     Free fm -> nt1 fm >>= go
 = nt1 (fmap return fm) >>= go
 = fmap return (nt1 fm) >>= go
 = nt1 fm >>= go . return  -- go . return = return, we just proved above
 = nt1

go $ inr ma
 = do v <- nt2 . runFreeT $ FreeT (fmap Pure ma)
      case v of
        Pure a  -> return a
        Free fm -> nt1 fm >>= go
 = do v <- fmap Pure (nt2 ma)
      case v of
        -- v is always (Pure a)!
        Pure a  -> return a
        Free fm -> nt1 fm >>= go
 = do a <- nt2 ma
      return a
 = nt2 ma
```

**(3)** `eitherFreeT` has "naturality"

`eitherFreeT` has "naturality" in the following sense: for all `nt1 :: f ~> n, nt2 :: m ~> n`
and `after :: n ~> n'` where `nt2` and `after` are monad morphisms,
`after . eitherFreeT nt1 nt2 = eitherFreeT (after . nt1) (after . nt2)`.

```haskell
go = eitherFreeT nt1 nt2
after . go $ ma
 = after $ do
     v <- nt2 (runFreeT ma)
     case v of
       Pure a  -> return a
       Free fm -> nt1 fm >>= go
 = do v <- after . nt2 $ runFreeT ma
      case v of
        Pure a  -> after (return a)
        Free fm -> after (nt1 fm >>= go)
 = do v <- (after . nt2) $ runFreeT ma
      case v of
        Pure a  -> return a
        Free fm -> (after . nt1) fm >>= (after . go)

go' = eitherFreeT (after . nt1) (after . nt2)
go' ma
 = do v <- (after . nt2) $ runFreeT ma
      case v of
        Pure a  -> return a
        Free fm -> (after . nt1) fm >>= go'
```

`after . go` and `go'` are equal by induction.

**(4)** Such monad morphism is unique

Suppose `nt' :: FreeT f m ~> n` is a monad morphism with a property
`nt' . inl = nt1` and `nt' . inr = nt2`. It can be shown that `nt' = eitherFreeT nt1 nt2`.

*Lemma 4-1.* `eitherFreeT inl inr = id`

```haskell
go = eitherFreeT inl inr

go ma
 = do v <- inr $ runFreeT ma
      case v of
        Pure a  -> return a
        Free fm -> inl fm >>= go
 = do v <- lift $ runFreeT ma
      case v of
        Pure a  -> return a
        Free fm -> liftF fm >>= go
 = do v <- FreeT $ fmap Pure $ runFreeT ma
      case v of
        Pure a  -> return a
        Free fm -> (FreeT $ return (Free (fmap return fm))) >>= go
 = FreeT $ do
     vv <- fmap Pure $ runFreeT ma
     case vv of
       Pure v -> case v of
         Pure a  -> runFreeT $ return a
         Free fm -> runFreeT $ (FreeT $ return (Free (fmap return fm))) >>= go
       Free _ -> {- Omit -}
 = FreeT $ do
     v <- runFreeT ma
     case v of
       Pure a  -> runFreeT $ return a
       Free fm -> runFreeT $ (FreeT $ return (Free (fmap return fm))) >>= go
 = FreeT $ do
     v <- runFreeT ma
     case v of
       Pure a  -> runFreeT $ FreeT $ return (Pure a)
       Free fm -> runFreeT $ FreeT $
         do v2 <- return (Free (fmap return fm)))
            case v2 of
              Pure _  -> {- Omit -}
              Free fm -> return $ Free (fmap (>>= go) fm)
 = FreeT $ do
     v <- runFreeT ma
     case v of
       Pure a  -> return (Pure a)
       Free fm -> return $ Free (fmap (>>= go) (fmap return fm))
 = FreeT $ do
     v <- runFreeT ma
     return $ case v of
       Pure a  -> Pure a
       Free fm -> Free (fmap go fm)
 = FreeT . fmap (bimap id go) . runFreeT $ ma
 = fmap id ma
 = ma
```

By naturality and Lemma 4-1, 

```haskell
eitherFreeT nt1 nt2
 = eitherFreeT (nt' . inl) (nt' . inr)
 = nt' . eitherFreeT inl inr
 = nt'
```

Thus there are only one monad morphism with these properties.

### Corollary of the universal property

`transFreeT_` maps "left" component of `FreeT f m`,
and commutes with `eitherFreeT` in very expected way.

```haskell
transFreeT_ f . inr
 = transFreeT_ f . FreeT . fmap Pure
 = FreeT . fmap Pure
 = inr

transFreeT_ f . inl
 = transFreeT_ f . FreeT . return . Free . fmap return
 = FreeT . return . Free . f . fmap (transFreeT_ f . return)
 = FreeT . return . Free . fmap return . f
 = inl . f

-- By uniqueness of the morphism:
transFreeT_ f = eitherFreeT (inl . f) inr

-- Combining the above with naturality:
eitherFreeT nt1 nt2 . transFreeT_ f
 = eitherFreeT (eitherFreeT nt1 nt2 . transFreeT_ f . inl)
               (eitherFreeT nt1 nt2 . transFreeT_ f . inr)
 = eitherFreeT (eitherFreeT nt1 nt2 . inl . f) (eitherFreeT nt1 nt2 . inr)
 = eitherFreeT (nt1 . f) (nt2)
```

### `FMonad` laws

To ignore newtype wrapping, I'll use the following instead of `ffmap, fpure, fjoin`:

```haskell
ffmap_ :: (Functor f, Functor m) => (f ~> g) -> (FreeT f m ~> FreeT g m)
ffmap_ = transFreeT_

fpure_ :: (Functor f, Monad m) => f ~> FreeT f m
fpure_ = inl

fjoin_ :: (Functor f, Monad m) => FreeT (FreeT f m) m ~> FreeT f m
fjoin_ = retractT
```

`fjoin_ = eitherFreeT id inr` by the following transformation of the definition:

```haskell
fjoin_ = retractT_
 = do val <- lift m
      case val of
        Pure x -> return x
        Free y -> y >>= retractT
 = do val <- inr m
      case val of
        Pure x -> return x
        Free y -> id y >>= retractT
 = eitherFreeT id inr
```

**Left Unit**: `fjoin_ . fpure_ = id`

`fjoin_ . fpure_ = eitherFreeT id inr . inl = id` by the property of `eitherFreeT`.

**Right Unit**: `fjoin_ . ffmap_ fpure_`

Can be calculated using the universal property.

```haskell
ffmap_ fpure_
 = transFreeT_ inl
 = eitherFreeT (inl . inl) inr
fjoin_ . ffmap fpure_
 = eitherFreeT id inr . eitherFreeT (inl . inl) inr 
 = eitherFreeT (eitherFreeT id inr . inl . inl) (eitherFreeT id inr . inr)
 = eitherFreeT inl inr
 = id
```

**Associativity**: `fjoin_ . fjoin_ = fjoin_ . ffmap_ fjoin_`

```hasekell
fjoin_ . fjoin_
 = eitherFreeT id inr . eitherFreeT id inr
 = eitherFreeT (eitherFreeT id inr . id) (eitherFreeT id inr . inr)
 = eitherFreeT (eitherFreeT id inr) inr
 = eitherFreeT id inr . transFreeT_ (eitherFreeT id inr)
 = fjoin_ . ffmap_ fjoin_
```

## Note

`inl, inr, eitherFreeT` looks like `Left, Right, either`.
So it is tempting to say `FreeT (FreeT f n) m` and `FreeT f (FreeT n m)`
are isomophic by the following way:

```haskell
assoc :: FreeT f (FreeT n m) ~> FreeT (FreeT f n) m 
assoc = eitherFreeT (inl . inl) (eitherFreeT (inl . inr) inr)

disassoc :: FreeT (FreeT f n) m ~> FreeT f (FreeT n m)
disassoc = eitherFreeT (eitherFreeT inl (inr . inl)) (inr . inr)
```

But this is not the case! In the `disassoc` function,
it uses `inr . inl` as a monad morphism.
While `inr . inl :: n ~> FreeT f (FreeT n m)` is a natural transformation
between `Monad`s, it is not a monad morphism.

By this lack of condition, you can't prove `disassoc . assoc = id`.
You shouldn't be able to ---- because they are *not* isomorphism.

`FreeT t u` has the following "nesting structure" of functors t,u:

```
FreeT t u ~ u ∘ t ∘ u ∘ t ∘ ･･･ ∘ t ∘ u

(1u = u made by applying `return @u`)
inl t = 1u ∘ t ∘ 1u
inr u = u
```

So nesting of `FreeT (FreeT f n) m` is, for example,

```
  m ∘ FreeT f n         ∘ m ∘ FreeT f n             ∘ m
= m ∘ (n ∘ f ∘ ･･･ ∘ n) ∘ m ∘ (n ∘ f ∘ n ∘ ･･･ ∘ n) ∘ m
```

And for `FreeT f (FreeT n m)`:

```
  FreeT n m             ∘ f ∘  FreeT n m            ∘ f ∘ FreeT n m
= (m ∘ n ∘ m ∘ ･･･ ∘ m) ∘ f ∘ (m ∘ n ∘ m ∘ ･･･ ∘ m) ∘ f ∘ (m ∘ n ∘ m ∘ ･･･ ∘ m)
```

Using this notation, a counterexample for they are not inverses look like this:

```
      (:: FreeT (FreeT f n) m)
  m ∘ FreeT f n   ∘ m
= m ∘ (n ∘ f ∘ n) ∘ m
   || (disassoc)
   vv
  m ∘ (1m ∘ n ∘ 1m) ∘ (1m ∘ f ∘ 1m) ∘ (1m ∘ n ∘ 1m) ∘ m
=  m ∘ n ∘ 1m  ∘ f ∘  1m ∘ n ∘ m
= (m ∘ n ∘ 1m) ∘ f ∘ (1m ∘ n ∘ m)
   || (assoc)
   vv
  m ∘ (1m ∘ n ∘ 1m) ∘ 1m ∘ (1m ∘ 1n ∘ f ∘ 1n ∘ 1m) ∘ 1m ∘ (1m ∘ n ∘ 1m) ∘ m
= m ∘ (n) ∘ 1m ∘ (1n ∘ f ∘ 1n) ∘ 1m ∘ (n) ∘ m
```
