# On `FreeT' m` being lawful `FMonad`

## Definitions

### FFunctor and FMonad

`FFunctor` ([code](./FMonad.hs#L58))

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

`FMonad` ([code](./FMonad.hs#L117))

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

[FreeT'](./ListTVia.hs#L30), cf. [FreeT](https://hackage.haskell.org/package/free-5.1.3/docs/Control-Monad-Trans-Free.html#t:FreeT)

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

-- Same!
transFreeT_ :: forall f g m. (Functor f, Functor m) => (f ~> g) -> FreeT f m ~> FreeT g m
transFreeT_ fg =
  let fg' :: forall a. FreeF f a ~> FreeF g a
      fg' (Pure a) = Pure a
      fg' (Free fr) = Free (fg fr)

      go :: FreeT f m ~> FreeT g m
      go (FreeT mfx) = FreeT $ fmap (fg' . fmap go) mfx
  in go

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
```

### Monad morphism

Natural transformation between `Functor`s `nt :: f ~> g` is a
monad morphism iff

* `nt . return @f = return @g`
* `nt . join @f = join @g . fmap nt . nt`

### Definitions for proof

``` haskell
ffirst :: (Monad m, Monad n, Functor f) => (m ~> n) -> (FreeT' m f ~> FreeT' n f)
ffirst nt = FreeT' . hoistFreeT nt . unFreeT'

hoistFreeT :: (Monad n, Functor f) => (m ~> n) -> (FreeT f m ~> FreeT f n)
hoistFreeT nt = FreeT . nt . fmap (fmap (hoistFreeT nt)) . runFreeT

fsecond :: (Functor m, Functor f, Functor g) => (f ~> g) -> (FreeT' m f ~> FreeT' m g)
fsecond = ffmap

inl :: (Monad m) => m ~> FreeT' m f
inl = FreeT' . lift
inl mx = FreeT' . FreeT $ fmap Pure mx

inr :: (Functor f, Monad m) => f ~> FreeT' m f
inr = fpure
inr gx = FreeT' (liftF gx)
       = FreeT' . FreeT . return @m . Free . fmap (return @(FreeT m f)) $ mx

nabla :: (Monad m) => FreeT' m m ~> m
nabla = runIdentityT . foldFreeT IdentityT . unFreeT'

-- Copy-pasted from "free"
foldFreeT :: (Monad m, MonadTrans t, Monad (t m)) => (f ~> t m) -> (FreeT f m ~> t m)
foldFreeT f (FreeT m) = lift m >>= foldFreeF
  where
    foldFreeF (Pure a) = return a
    foldFreeF (Free as) = f as >>= foldFreeT f
```

### Lemma

I'll use these equations for `return` and `join` of
`FreeT`:

```haskell
return @(FreeT f m) = FreeT . return @m . Pure
join (FreeT m) = FreeT $
  m >>= \v -> case v of
    Pure a -> runFreeT a
    Free w -> return (Free (fmap join w))
join = FreeT . join . fmap (fromFreeF runFreeT (return . Free . fmap join)) . runFreeT

fromFreeF :: (a -> r) -> (f b -> r) -> FreeF f a b -> r
```

Use the following lemma several times:

```haskell
fmap f . join
 = FreeT . fmap (bimap f (fmap f)) . runFreeT .
   FreeT . join . fmap (fromFreeF runFreeT (return . Free . fmap join)) . runFreeT
 = FreeT . fmap (bimap f (fmap f)) .
   join . fmap (fromFreeF runFreeT (return . Free . fmap join)) . runFreeT
 = FreeT . join .
   fmap (fmap (bimap f (fmap f))) .
   fmap (fromFreeF runFreeT (return . Free . fmap join)) . runFreeT
 = FreeT . join .
   fmap (fmap (bimap f (fmap f)) .
         fromFreeF runFreeT (return . Free . fmap join)) .
   runFreeT
 = FreeT . join .
   fmap (fromFreeF (fmap (bimap f (fmap f)) . runFreeT)
                   (fmap (bimap f (fmap f)) . (return . Free . fmap join))) .
   runFreeT
 = FreeT . join .
   fmap (fromFreeF (runFreeT . fmap f)
                   (return . bimap f (fmap f) . Free . fmap join)) .
   runFreeT
 = FreeT . join .
   fmap (fromFreeF (runFreeT . fmap f)
                   (return . Free . fmap (fmap f) . fmap join)) .
   runFreeT
 = FreeT . join .
   fmap (fromFreeF (runFreeT . fmap f) (return . Free . fmap (fmap f . join))) .
   runFreeT
```


## Proof 

### Lemma (universality)

**Statement:** Let `m,n` be a `Monad`, `f` be a `Functor`.
For all monad morphism `nt1 :: m ~> n` and natural transformation `nt2 :: f ~> n`, there exists
a unique monad morphism `nt :: FreeT' m f ~> n` with properties

* `nt . inl = nt1`
* `nt . inr = nt2`

**Proof:**

The following `eitherFreeT nt1 nt2` is the monad morphism `FreeT' m f ~> n`.

```haskell
eitherFreeT :: (Monad m, Monad n, Functor f) => (m ~> n) -> (f ~> n) -> (FreeT' m f ~> n)
eitherFreeT nt1 nt2 = go . unFreeT'
  where
    go ma =
      do v <- nt1 (runFreeT ma)
         case v of
           Pure a  -> return a
           Free fm -> nt2 fm >>= go
```

**(1)** It is actually a monad morphism. `go . return = return` is straightforward.

```haskell
go $ return a
  = go (FreeT (return (Pure a)))
  = do v <- nt1 (return (Pure a))
       case v of
         Pure a  -> return a
         Free fm -> nt2 fm >>= go
    -- nt1 . return = return
  = case Pure a of
      Pure a  -> return a
      Free fm -> nt2 fm >>= g0
  = return a
```

`go . join = join . fmap go . go` is shown inductively.

```hasekll
join . fmap go . go $ mma
 = go mma >>= go
 = do v <- nt1 $ runFreeT mma
      ma' <- case v of
        Pure ma -> return ma
        Free fm -> nt2 fm >>= go
      go ma'
 = do v <- nt1 $ runFreeT mma
      case v of
        Pure ma -> return ma     >>= go
        Free fm -> nt2 fm >>= go >>= go
 = do v <- nt1 $ runFreeT mma
      case v of
        Pure ma -> go ma
        Free fm -> nt2 fm >>= join . fmap go . go

go $ join mma
  = go . FreeT $ runFreeT mma >>= \v -> case v of
      Pure a  -> runFreeT a
      Free fm -> return (Free (fmap join fm))
  = do v' <- nt1 $ do
         v <- runFreeT mma
         case v of
           Pure ma -> runFreeT ma
           Free fm -> return $ Free (fmap join fm)
       case v' of
         Pure a  -> return a
         Free fm -> nt2 fm >>= go
    -- nt1 is a monad morphism
  = do v <- nt1 mma
       v' <- case v of
         Pure ma -> nt1 $ runFreeT ma
         Free fm -> return $ Free (fmap join fm)
       case v' of
         Pure a  -> return a
         Free fm -> nt2 fm >>= go
  = do v <- nt1 mma
       case v of
         Pure ma -> do
           ---- This part is equal to (go ma) ----
           v' <- nt1 $ runFreeT ma
           case v' of
             Pure a  -> return a
             Free fm -> nt2 fm >>= go
           ---------------------------------------
         Free fm -> nt2 (fmap join fm) >>= go
  = do v <- nt1 mma
       case v of
         Pure ma -> go ma
         Free fm -> nt2 fm >>= go . join
```

