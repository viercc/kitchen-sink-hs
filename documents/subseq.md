```haskell
implies :: Bool -> Bool -> Bool
implies = (<=)
{- Bool is category, morphisms are
   valid equations (x `implies` y = True)
-}

type Pred a = a -> Bool
{- Every (p :: Pred a) is a functor
    (discrete category |a| -> Bool)
   
   Natural morphism Pred(p,q) is
     forall x::a. p x `implies` q x
   
   Example
   p1 = (>= 0) :: Pred Int
   p2 = (>= 100) :: Pred Int

   There are:
      Pred(const False, const True)
      Pred(const False, p1)
      Pred(p1, p2)
    There are not:
      Pred(p2, p1)
-}

(⊑) :: (Eq a) => [a] -> [a] -> Bool
(⊑) = isSubsetOf
{-
  ⊑ is also a category, as all preorders are.

  as ⊑ as
  (as ⊑ bs), (bs ⊑ cs) implies (as ⊑ cs)

  ⊑ is also compatible with (++)
    as ⊑ bs ==> as ++ cs ⊑ bs ++ cs
    as ⊑ bs ==> cs ++ as ⊑ cs ++ bs
  
  ⊑
-}

filter :: (a -> Bool) -> [a] -> [a]
{-
  Specs of filter look like Bifunctor at this point
  
  first  :: (a -> a')   -> f      a x  -> f      a' x
            (Pred p p') => filter p as ⊑ filter p' as

  second :: (x  -> x')  -> f      a x  -> f      a x'
            (as ⊑ as') => filter p as ⊑ filter p as'
  
  And the rest of specs suspiciously similar to Comonad
  
             filter p as ⊑ as
  extract :: f        x  -> x
  
  filter p as = filter p (filter p as)
    <=> filter p (filter p as) ⊑ filter p as
    and           filter p as  ⊑ filter p (filter p as)
  
  fmap extract ::
    f        (f        x)  -> f        x
    filter p (filter p as) ⊑ filter p as
  duplicate ::
    f        x  -> f        (f        x)
    filter p as ⊑ filter p (filter p as)
-}

```
