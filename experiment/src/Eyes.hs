{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module Eyes where

import Data.Kind ( Type )
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Profunctor

-- Getter s a = s -> a
type Getter s a = s -> a 
type Setter s a = (a -> a) -> s -> s

-- Example
data V2 a = V2 a a
  deriving Functor

instance Applicative V2 where
  pure a = V2 a a
  V2 f1 f2 <*> V2 x1 x2 = V2 (f1 x1) (f2 x2)

instance Monad V2 where
  return = pure
  V2 a1 a2 >>= f =
    V2 (let V2 b1 _ = f a1 in b1)
       (let V2 _ b2 = f a2 in b2)

---------------------------------------------------------
-- Distributive implies "there's a tuple of getters"
---------------------------------------------------------

-- Distributive
class Functor t => Distributive t where
  distribute :: Functor f => f (t a) -> t (f a)

-- Distributive => Getters

getters :: Distributive t => t (Getter (t a) a)
getters = distribute id
  -- id :: t a -> t a
  -- id :: (f ~ Getter (t a)) => f (t a)

-- Distributive implies Monad
pureD :: forall t a. Distributive t => a -> t a
pureD = fmap getConst . distribute . Const

joinD :: forall t a. Distributive t => t (t a) -> t a
joinD tta = fmap (\get -> get . fmap get $ tta) getters

---------------------------------------------------------
-- Logistic <==> "there's a tuple of setters"
---------------------------------------------------------

class Functor t => Logistic t where
  deliver :: Contravariant f => f (t a -> t a) -> t (f (a -> a))
  deliver ret = fmap (\set -> contramap set ret) setters
  
  setters :: t (Setter (t a) a)
  setters = getOp <$> deliver (Op id)

instance Logistic V2 where
  setters = V2 (\f (V2 a b) -> V2 (f a) b)
               (\f (V2 a b) -> V2 a (f b))

---------------------------------------------------------
-- Representable t (==> Distributive t) ==> getters
-- Representable t + Eq (Key t) ==> setters
---------------------------------------------------------

class Functor t => Representable t where
  type Key t :: Type
  index :: t a -> Key t -> a
  tabulate :: (Key t -> a) -> t a
  -- tabulate . index = id
  -- index . tabulate = id

gettersRep :: Representable t => t (Getter (t a) a)
gettersRep = tabulate $ \k ta -> index ta k

settersRep :: (Representable t, Eq (Key t)) => t (Setter (t a) a)
settersRep = tabulate $ \k f ta ->
  tabulate $ \j -> if j == k then f (index ta j) else index ta j

---------------------------------------------------------
-- Eq (Key t) 〜 (Key t -> Key t -> Bool) 〜 t (t Bool)
---------------------------------------------------------
class Diag t where
   diag :: t (t Bool)

instance Diag V2 where
  diag = V2 (V2 True False) (V2 False True)

-- Remember that Distributive t ==> Monad t
settersDiag :: forall t a. (Monad t, Diag t) => t (Setter (t a) a)
settersDiag = toSetter <$> diag
  where
    toSetter :: t Bool -> (a -> a) -> (t a -> t a)
    toSetter ek f ta = ek >>= \equals -> ta >>= \a -> return (if equals then f a else a)

diagSetters :: forall t. (Monad t, Logistic t) => t (t Bool)
diagSetters = fromSetter <$> setters
  where
    fromSetter :: Setter (t Bool) Bool -> t Bool
    fromSetter set = set (const True) (pure False)


---------------------------------------------------------
-- Eyes
---------------------------------------------------------

-- Iso s a  = forall p. Profunctor p => p a a -> p s s
-- Lens s a = forall p. Strong p => p a a -> p s s

-- lenses :: t (Lens (t a) a)

-- getters = distribute @(Getter (t a)) id
-- distribute :: Functor f => f (t a) -> t (f a)
-- distribute @(Getter (t a)) :: (t a -> t a) -> t (t a -> a)

-- Contravariant g
-- g' r a = g' a -> r
-- Functor (g' r)

-- Setter (t a) a = a -> t a -> t a
--  ~ t a -> a -> t a
-- 
-- t a -> (a -> t r) -> t r
-- =================================
-- t a -> t a -> t (t a)

-- Setter

class Profunctor p => ProductProfunctor p where
    punit :: p () ()
    pprod :: p a b -> p a' b' -> p (a,a') (b,b')

class Distributive t => Eyes t where
  eyes :: Profunctor p => p (t a) (t a) -> t (p a a)
