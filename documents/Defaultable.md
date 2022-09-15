```haskell
union :: Semialign f => f a -> f a -> f a
union = alignWith fromThese
      = \x y -> fromThese <$> align x y

fromThese :: These x x -> x
fromThese
  = these id id const
  = \case
       This x -> x
       That y -> y
       These x _ -> x

Notation "x <> y" := union x y.

Lemma [Union-Associativity]
  (x <> y) <> z = x <> (y <> z)
  -- Uses [Align/Associativity]
Proof omitted.

apZip :: Zip f => f (a -> b) -> f a -> f b
apZip = zipWith ($)
      = \x y -> ev <$> zip x y

ev :: (a -> b, a) -> b
ev (f,a) = f a

Notation "x <.> y" := apZip x y.

Pose (pure f <.> x = f <$> x).
Pose (f <$> x <.> y = zipWith f x y).

Lemma [ApZip-Composition]
  (.) <$> x <.> y <.> z = x <.> (y <.> z).
  -- Uses [Zip/Associativity]
Proof omitted.

Lemma [Distribute-ApZip-Union-Right]
  union x y <.> z = x <.> z <> y <.> z.

Proof.
union x y <.> z
   -- Definitions
 = fmap ev $ zip (x <> y) z
 = fmap ev $ zip (fmap fromThese (align x y)) z
   -- Naturality of zip
 = fmap (ev . first fromThese) $ zip (align x y) z
   -- [aux]
 = fmap (fromThese . bimap ev ev . distrPairThese) $ zip (align x y) z
   -- [Zip/Distributivity]
 = fmap (fromThese . bimap ev ev) $ align (zip x z) (zip y z)
   -- Naturality of align
 = fmap fromThese $ align (ev <$> zip x z) (ev <$> zip y z)
   -- Definition
 = fmap ev (zip x z) <> fmap ev (zip y z) 
 = x <.> z <> y <.> z

[aux] ev . first fromThese
        = fromThese . bimap ev ev . distrPairThese
  Proof.
  (LHS)
   = \(xy, z) -> case xy of
        This x -> x z
        That y -> y z
        These x _ -> x z
  (RHS)
   = \(x, yz) -> fromThese $ case yz of
        This x -> This (ev (x,z))
        That y -> That (ev (y,z))
        These x y -> These (ev (x,z)) (ev (y,z))
   = \(x, yz) -> case yz of
        This x -> ev (x,z)
        That y -> ev (y,z)
        These x y -> ev (x,z)
   = \(x,yz) -> case yz of
        This y -> x y
        That z -> x z
        These y z -> x (const y z)
   = (LHS)
  End.
End.

Lemma [Distribute-ApZip-Union-Left]
  x <.> (y <> z) = x <.> y <> x <.> z.
Proof omitted.



[Applicative/Composition]
  pure (.) <*> u <*> v <*> w = u <*> (v <*> w)

u :: Defaultable map (b -> c)
v :: Defaultable map (a -> b)
w :: Defaultable map a

u = Defaultable uMap (Just ud)
v = Defaultable vMap (Just vd)
w = Defaultable wMap (Just wd)


Proof.
(LHS)
  = pure (.) <*> u <*> v <*> w
    -- TODO: prove this step
  = (.) <$> u <*> v <*> w
  = uv <*> w
    where
      uv = Defaultable uvMap (Just (ud . vd))
      uvMap = (.) <.> uMap <.> vMap
           <> fmap (ud .) vMap
           <> fmap (. vd) uMap
  = Defaultable uvwMap (Just (ud (vd wd)))
    where
      uvwMap = uvMap <.> wMap
            <> fmap (ud . vd) wMap
            <> fmap ($ wd) uvMap
      uvMap = zipWith (.) uMap vMap
           <> fmap (ud .) vMap
           <> fmap (. vd) uMap
    -- substitute uvMap and [Distribute-ApZip-Union-Right]
    -- Naturality of union
  = Defaultable uvwMap (Just (ud (vd wd)))
    where
      uvwMap = (.) <$> uMap <.> vMap <.> wMap
            <> fmap (ud .) vMap <.> wMap
            <> fmap (. vd) uMap <.> wMap
            <> fmap (ud . vd) wMap
            <> fmap ($ wd) ((.) <$> uMap <.> vMap)
            <> fmap ($ wd) (fmap (ud .) vMap)
            <> fmap ($ wd) (fmap (vd .) uMap)
    -- Float fmap up by naturality
  = Defaultable uvwMap (Just (ud (vd wd)))
    where
      uvwMap = fmap (\u v w -> u (v w)) uMap <.> vMap <.> wMap
            <> fmap (\v w -> ud (v w))           vMap <.> wMap
            <> fmap (\u w -> u (vd w))  uMap <.>          wMap
            <> fmap (\w -> ud (vd w))                     wMap
            <> fmap (\u v -> u (v wd))  uMap <.> vMap
            <> fmap (\v -> ud (v wd))            vMap
            <> fmap (\u -> u (vd wd))   uMap

(RHS)
  = u <*> (v <*> w)
  = u <*> vw
    where
      vw = Defaultable vwMap (Just (vd wd))
      vwMap = vMap <.> wMap
           <> fmap vd wMap
           <> fmap ($ wd) vMap
  = Defaultable uvwMap (Just (ud (vd wd)))
    where
      uvwMap = uMap <.> vwMap
            <> fmap ud vwMap
            <> fmap ($ vd wd) uvMap
      vwMap = vMap <.> wMap
           <> fmap vd wMap
           <> fmap ($ wd) vMap
    -- substitute vwMap and [Distribute-ApZip-Union-Left]
    -- Naturality of union
  = Defaultable uvwMap (Just (ud (vd wd)))
    where
      uvwMap = uMap <.> (vMap <.> wMap)
            <> uMap <.> fmap vd wMap
            <> uMap <.> fmap ($ wd) vMap
            <> fmap ud (vMap <.> wMap)
            <> fmap ud (fmap vd wMap)
            <> fmap ud (fmap ($ wd) vMap)
            <> fmap ($ vd wd) uMap
    -- [ApZip-Composition]
    -- Float fmap up by naturality
  = Defaultable uvwMap (Just (ud (vd wd)))
    where
      uvwMap = fmap (\u v w -> u (v w)) uMap <.> vMap <.> wMap
            <> fmap (\u w -> u (vd w))  uMap <.>          wMap
            <> fmap (\u v -> u (v wd))  uMap <.> vMap
            <> fmap (\v w -> ud (v w))           vMap <.> wMap
            <> fmap (\w -> ud (vd w))                     wMap
            <> fmap (\v -> ud (v wd))            vMap
            <> fmap (\u -> u (vd wd))   uMap
```

Lemma [Shadowed-Commute]:
    Parameter
      a b c :: Type
      m :: Type -> Type
      Zip m
      
      f :: a -> b -> c
      g :: a -> c
      h :: b -> c
      x :: f a
      y :: f b
      
        fmap f x <.> y <> fmap g x <> fmap h y
      = fmap f x <.> y <> fmap h y <> fmap g x
Proof.
  Let reorder :: These (These x b) a -> These (These x a) b
      reorder = unassocThese . second swapThese . assocThese
  
  
  
    fmap f x <.> y <> fmap g x <> fmap h y
  = fmap fromThese $ fmap fromThese (fmap (uncurry f) (zip x y) `align` fmap g x) `align` fmap h y
  = fmap (fromThese . bimap (fromThese . bimap (uncurry f) g) h) $ (zip x y `align` x) `align` y
  = fmap fgh (zip x y `align` x `align` y)
    where
      fgh :: These (These (a,b) a) b -> c
      fgh = fromThese . first fromThese . bimap (bimap (uncurry f) g) h
  = fmap fgh' (zip x y `align` y `align` x)
      fgh' :: These (These (a,b) b) a -> c
      fgh' = fromThese . first fromThese . bimap (bimap (uncurry f) g) h
