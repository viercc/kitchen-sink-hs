{-# LANGUAGE DeriveFunctor #-}
module Extrude(extrude) where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Foldable (Foldable(..))

extrude :: Traversable t => t (NonEmpty a) -> (t a, [a])
extrude = runQ . traverse ex

newtype Q a b = Q { unQ :: [a] -> [a] -> (b, [a], [a]) }
    deriving Functor

instance Applicative (Q a) where
    pure b = Q $ \ins outs -> (b, ins, outs)
    qx <*> qy = Q $ \ins outs ->
        let ~(x, ins', outs'') = unQ qx ins outs'
            ~(y, ins'', outs') = unQ qy ins' outs
        in (x y, ins'', outs'')

runQ :: Q a b -> (b, [a])
runQ qb =
   let ~(b, ins, outs) = unQ qb outs []
   in (b, ins)

ex :: NonEmpty a -> Q a a
ex as = Q $ \ins outs -> case unsafeHeadTail ins of
    ~(a0, ins') -> (a0, ins', toList as ++ outs)

unsafeHeadTail :: [a] -> (a, [a])
unsafeHeadTail [] = error "Empty! misused queue?"
unsafeHeadTail (a:as) = (a, as)