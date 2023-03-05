module HyperCont where

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import Control.Monad.Hyper
import Data.Profunctor
import Control.Monad (ap)

newtype HC r a = HC {runHC :: Hyper (Hyper a r) r }

instance Functor (HC r) where
    fmap f (HC ma) = HC $ lmap (lmap f) ma

instance Applicative (HC r) where
    pure = HC . unit
    (<*>) = ap

-- Hyper r () is isomorphic to ()
trivial :: Hyper r ()
trivial = pure ()

-- Hyper () r is isomorphic to r
uninteresting :: Hyper () r -> r
uninteresting p = invoke p trivial

-- We really can do nothing better than this!
-- Maybe when we can touch @r@?
unit1 :: Hyper (Hyper () r) r
unit1 = arr uninteresting

-- ANY unit function must be the following form by yoneda lemma!
unit :: a -> Hyper (Hyper a r) r
unit a = lmap (lmap (const a)) unit1

instance Monad (HC r) where
    ma >>= f = HC . join_ . runHC . fmap (runHC . f) $ ma

join_ :: Hyper (Hyper (Hyper (Hyper a r) r) r) r -> Hyper (Hyper a r) r
join_ = lmap unit

{-
p . q = Hyper $ \k -> invoke p (q . k)

r :: Type
a :: Type
p :: Hyper a r

go = lmap unit (unit p) :: Hyper a r
 = unit p . arr unit
 = Hyper $ \k ->
     invoke (unit p) (arr unit . k)
invoke go k
 = invoke (unit p) (arr unit . k)
 = project (invoke (arr unit . k) (unit p)) p
 = project (invoke (arr unit) (k . unit p)) p
 = project (unit (invoke (k . unit p) (arr unit))) p
 = project (unit (invoke k (unit p . arr unit))) p
 = project (unit (invoke k go)) p
 = invoke (unit (invoke k go)) (pure p)
-}

{-
fmap_ f = lmap (lmap f)

(A) lmap unit . unit = id
-------------------------- (A) implies all of the monad laws
(1) join_ . unit = id
(2) join_ . fmap_ unit
 = lmap unit . lmap (lmap unit)
 = lmap (lmap unit . unit)
 = lmap id
 = id
(3) join_ . join_
 = lmap unit . lmap unit
 = lmap (unit . unit)
 = lmap (fmap_ unit . unit)
 = lmap (lmap (lmap unit) . unit)
 = lmap unit . lmap (lmap (lmap unit))
 = join_ . fmap_ join_
-}
