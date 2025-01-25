{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DeriveFunctor #-}

{-# LANGUAGE ImplicitParams #-}
-- Distributive laws for comonad!
module Comonad.Dist where

import Data.Functor.Classes (Eq1)

import Control.Comonad

type Dist w v = forall x. w (v x) -> v (w x)

eqv :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
eqv = liftA2 (==)

distLaw1, distLaw2, distLaw3, distLaw4 
  :: forall w v x. (Comonad w, Comonad v, Eq1 w, Eq1 v, Eq x) => Dist w v -> w (v x) -> Bool
distLaw1 dist = (extract @v . dist) `eqv` (fmap @w (extract @v))
distLaw2 dist = (fmap (extract @w) . dist) `eqv` (extract @w)
distLaw3 dist = (duplicate @v . dist) `eqv` (fmap dist . dist . fmap (duplicate @v))
distLaw4 dist = (fmap (duplicate @w) . dist) `eqv` (dist . fmap dist . duplicate @w)

data Store s a = Store s (s -> a)
  deriving Functor

peek :: Store s a -> s -> a
peek (Store _ f) = f 
pos :: Store s a -> s
pos (Store s _) = s

instance Comonad (Store s) where
  extract (Store s f) = f s
  duplicate (Store s f) = Store s $ \s' -> Store s' f

-- Store-Store distributive laws
distSS :: forall s t x. Store s (Store t x) -> Store t (Store s x)
distSS st@(Store s0 f) = ts
  where
    g :: s -> t
    g = \s -> pos (f s)

    p0 :: Store s t
    p0 = Store s0 g

    h :: (s, t) -> x
    h = \(s,t) -> peek (f s) t

    q0 = distPos p0
    f' = h . distPeek p0
    ts = Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> f' (t', s')

distPos :: Store s t -> Store t s
distPos = undefined

distPeek :: Store s t -> (t, s) -> (s, t)
distPeek = undefined

----------------------

-- Proof section

-- Parameters:
--
-- s,t :: Type

st :: forall s t. (?p0 :: Store s t) => Store s (Store t (s,t))
st = Store (pos ?p0) $ \s -> Store (peek ?p0 s) $ \t -> (s,t)

q0 :: forall s t. (?p0 :: Store s t) => Store t s
q0 = distPos ?p0

dl :: (?p0 :: Store s t) => t -> s -> s
dl t' s' = fst $ distPeek ?p0 (t',s')

dr :: (?p0 :: Store s t) => t -> s -> t
dr t' s' = snd $ distPeek ?p0 (t',s')

-- distSS in terms of q0, dl, dr
distDef :: forall s t. (?p0 :: Store s t) => [ Store t (Store s (s,t)) ]
distDef =
  [ distSS st
  , Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> (dl t' s', dr t' s')
  ]

-- From Law1:
eq1 :: forall s t. (?p0 :: Store s t) => [ Store s (s,t) ]
eq1 =
  -- LHS
  [
    extract (distSS st),
    extract $ Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> (dl t' s', dr t' s'),
    Store (peek q0 (pos q0)) $ \s' -> (dl (pos q0) s', dr (pos q0) s'),
    Store (extract q0) $ \s' -> (dl (pos q0) s', dr (pos q0) s')
  ] ++
  -- RHS
  [
    fmap extract st,
    Store (pos ?p0) $ \s -> (s, peek ?p0 s)
  ]

-- Hence:
eq1_1 :: forall s t. (?p0 :: Store s t) => [ s ]
eq1_1 = [ extract q0, pos ?p0 ]

eq1_2 :: forall s t. (?p0 :: Store s t) => [ s -> s ]
eq1_2 = [ dl (pos q0), id ]

eq1_3 :: forall s t. (?p0 :: Store s t) => [ s -> t ]
eq1_3 = [ dr (pos q0), peek ?p0 ]

-- From Law2:
eq2 :: forall s t. (?p0 :: Store s t) => [ Store t (s,t) ]
eq2 =
  -- LHS
  [
    fmap extract (distSS st),
    fmap extract $ Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> (dl t' s', dr t' s'),
    Store (pos q0) $ \t' -> extract $ Store (peek q0 t') $ \s' -> (dl t' s', dr t' s'),
    Store (pos q0) $ \t' -> (dl t' (peek q0 t'), dr t' (peek q0 t'))
  ] ++
  -- RHS
  [
    extract st,
    Store (extract ?p0) $ \t -> (pos ?p0, t)
  ]

-- Hence:
eq2_1 :: forall s t. (?p0 :: Store s t) => [ t ]
eq2_1 = [ pos q0, extract ?p0 ]

eq2_2 :: forall s t. (?p0 :: Store s t) => [ t -> s ]
eq2_2 = [ \t' -> dl t' (peek q0 t'), const (pos ?p0) ]

eq2_3 :: forall s t. (?p0 :: Store s t) => [ t -> t ]
eq2_3 = [ \t' -> dr t' (peek q0 t'), id ]

-- From Law3: 
eq3 :: forall s t. (?p0 :: Store s t) => [ Store t (Store t (Store s (s,t))) ]
eq3 = 
  -- LHS
  [
    duplicate $ distSS st
  , duplicate $ Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> (dl t' s', dr t' s')
  , Store (pos q0) $ \t' -> Store t' $ \t'' -> Store (peek q0 t'') $ \s' -> (dl t'' s', dr t'' s')
  ] ++
  -- RHS
  [
    fmap distSS $ distSS $ fmap duplicate st
  , fmap distSS $ distSS $ Store (pos ?p0) $ \s -> Store (peek ?p0 s) $ \t1 -> Store t1 $ \t2 -> (s, t2)
  , fmap distSS $ distSS $ fmap (fmap shift) st
  , fmap (distSS . fmap shift) $ distSS st
  , fmap (distSS . fmap shift) $ Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> (dl t' s', dr t' s')
  , Store (pos q0) $ \t' -> distSS $ Store (peek q0 t') $ \s' -> shift (dl t' s', dr t' s')
  , Store (pos q0) $ \t' -> distSS $ Store (peek q0 t') $ \s' -> Store (dr t' s') $ \t2 -> (dl t' s', t2)
  , Store (pos q0) $ \t' -> Store (pos (q1 t')) $ \t'' -> Store (peek (q1 t') t'') $ \s'' -> (dl t' (dl' t' t'' s''), dr' t' t'' s'')
  ]
  where
    shift (s,t1) = Store t1 $ \t2 -> (s, t2)
    p1 t' = Store (peek q0 t') (dr t')
    q1 t' = distPos (p1 t')
    dl' t' t'' s'' = fst $ distPeek (p1 t') (t'', s'')
    dr' t' t'' s'' = snd $ distPeek (p1 t') (t'', s'')

eq3_1 :: forall s t. (?p0 :: Store s t) => [ t -> t ]
eq3_1 =
  [ -- LHS
    id
    -- RHS
  , \t' -> pos (q1 t')
    -- From [ eq2_1 (?p0 := p1 t') ]
  , \t' -> extract (p1 t')
    -- By definition
  , \t' -> dr t' (peek q0 t')
    -- From [ eq2_3 (?p0 := p1 t') ]
  , id
  ]
  where
    p1 t' = Store (peek q0 t') (dr t')
    q1 t' = distPos (p1 t')

eq3_2 :: forall s t. (?p0 :: Store s t) => [ t -> t -> s ]
eq3_2 =
  [ -- LHS
    \_ -> peek q0
    -- RHS
  , \t' -> peek (q1 t')
  ]
  where
    p1 t' = Store (peek q0 t') (dr t')
    q1 t' = distPos (p1 t')

eq3_q1 :: forall s t. (?p0 :: Store s t) => [ t -> Store t s ]
eq3_q1 =
  [ 
    q1
  , \t' -> q1 t'
  , \t' -> Store (pos (q1 t')) (peek (q1 t'))
  , \t' -> Store t' (peek q0)
  ]
  where
    p1 t' = Store (peek q0 t') (dr t')
    q1 t' = distPos (p1 t')

{-

st = Store s0 $ \s -> Store (g s) $ \t -> (s,t)

    -- h :: (s,t) -> (s,t);  h = id

p0 = Store s0 g
q0 = distPos p0 :: Store t s
delta = distPeek p0 :: (t,s) -> (s,t)

distSS st = Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> delta (t', s')

[Law1] (extract @v . dist) === (fmap @w (extract @v))
  extract (distSS st)
   = 
   = 
   = Store (extract q0) $ \s' -> delta (pos q0, s')
  fmap extract st
   = 

  ==>:
    [e1-1] ... extract q0 = s0
    [e1-2] ... ∀s. delta (pos q0, s) = (s, g s)

[Law2] (fmap extract . dist) == extract
  fmap extract (distSS st)
   = fmap extract $ Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> delta (t', s')
   = Store (pos q0) $ \t' -> extract $ Store (peek q0 t') $ \s' -> delta (t', s')
   = Store (pos q0) $ \t' -> delta (t', peek q0 t')
  extract st
  = Store (g s0) $ \t -> (s0, t)

  ==>:
    [e2-1] ... g s0 = pos q0
    [e2-2] ... ∀t. delta (t, peek q0 t) = (s0, t)

[Law3] (duplicate @v . dist) === (fmap dist . dist . fmap (duplicate @v)) 

duplicate $ distSS st
 = duplicate $ Store (pos q0) $ \t' -> Store (peek q0 t') $ \s' -> delta (t', s')
 = Store (g s0) $ \t' -> Store t' $ \t'' -> Store (peek q0 t'') $ \s' -> delta (t'', s')
 = Store (g s0) $ \t' -> Store t' $ \t'' -> Store (peek q0 t'') $ \s' -> delta (t'', s')

fmap distSS . distSS . fmap (duplicate @v)
 = fmap distSS $ distSS $ Store s0 $ \s -> Store (g s) $ \t1 -> Store t1 $ \t2 -> (s, t2)
 = fmap distSS $ Store (g s0) $ \t1' -> Store (peek q0 t1') $ \s' ->
    let (s'', t1'') = delta (t1', s') in 
 = fmap distSS $ Store (g s0) $ \t1' -> Store (peek q0 t1') $ \s' -> Store (delta_2 t1' s') $ \t2 -> (t2, (delta_1 t1' s'))
    where delta_1 t s = fst (delta (t,s))
          delta_2 t s = snd (delta (t,s))
 = Store (g s0) $ \t1' ->
     distSS $ Store (peek q0 t1') $ \s' -> Store (delta_2 t1' s') $ \t2 -> (t2, (delta_1 t1' s'))
 = 

-}