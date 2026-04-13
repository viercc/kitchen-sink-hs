{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{- HLINT ignore "Use camelCase" -}
module Selective.Prism where

import Data.Bifunctor
import Control.Selective
import Control.Lens.Prism hiding (aside)

-- * Alternative formulations for 'Selective' class

-- ** Just Yoneda

-- | > select === selectWith id id
selectWith :: (Selective f) => (s -> Either a t) -> (r -> a -> t) -> f s -> f r -> f t
selectWith match_s op x y = select (match_s <$> x) (op <$> y)

{-

Free theorems:

[naturality-s]
  selectWith match_s op (h <$> x) y === selectWith (match_s . h) op x y

[naturality-r]
  selectWith match_s op x (h <$> y) === selectWith match_s (op . h) x y

[naturality-t]
  h <$> selectWith match_s op x y === selectWith (second h . match_s) ((h .) . op) x y

[naturality-a]
  selectWith (first h . match_s) op x y === selectWith match_s ((. h) . op) x y

-}

-- ** Emphasis on case analysis

-- | Apply only on Left
besides :: (Selective f) => f (Either a r) -> f (a -> b) -> f (Either b r)
besides = selectWith (second Right) (Left .)

-- | Recovering 'selectWith' from 'besides'
selectWith_besides :: (Functor f)
  => (forall a b r. f (Either a r) -> f (a -> b) -> f (Either b r))
  -> forall s a t r. (s -> Either a t) -> (r -> a -> t) -> f s -> f r -> f t
selectWith_besides besides' match_s op x y = nabla <$> besides' (match_s <$> x) (op <$> y)

{-

[selectWith -> besides -> selectWith]

selectWith_besides besides match_s op x y
 = nabla <$> besides (match_s <$> x) (op <$> y)
 = nabla <$> selectWith (second Right) (Left .) (match_s <$> x) (op <$> y)
 〈naturality-s, naturality-r〉
 = nabla <$> selectWith (second Right . match_s) ((Left .) . op) x y
 = nabla <$> selectWith (second Right . match_s) (\r a -> Left (op r a)) x y
 〈naturality-t〉
 = selectWith (second nabla . second Right . match_s) (\r a -> nabla (Left (op r a))) x y
 = selectWith (second id . match_s) (\r a -> id (op r a)) x y
 = selectWith match_s op x y

-}

-- ** Using Prism

-- | 'select' but split based on a @Prism@ given
selectP :: forall f s t a b.
    (Selective f)
  => APrism s t a b -> f s -> f (a -> b) -> f t
selectP p = withPrism p k 
  where
    k :: (b -> t) -> (s -> Either t a) -> f s -> f (a -> b) -> f t
    k inject_b match_s = selectWith (swapEither . match_s) (inject_b .)

-- | Recovering 'selectWith' from 'selectP'
selectWith_selectP :: (Functor f)
  => (forall s t a b. APrism s t a b -> f s -> f (a -> b) -> f t)
  -> forall s a t r. (s -> Either a t) -> (r -> a -> t) -> f s -> f r -> f t
selectWith_selectP selectP' match_s op x y =
  selectP' (prism id (swapEither . match_s)) x (op <$> y)

{-

[selectWith -> selectP -> selectWith]
selectWith_selectP selectP match_s op x y
 = selectP (prism id (swapEither . match_s)) x (op <$> y)
 = withPrism (prism id (swapEither . match_s))
     (\inject_b match' -> selectWith (swapEither . match') (inject_b .))
     x (op <$> y)
 〈withPrism/prism〉
 = let inject_b = id
       match' = swapEither . match_s
   in selectWith (swapEither . match') (inject_b .) x (op <$> y)
 = selectWith (swapEither . swapEither . match_s) id x (op <$> y)
 = selectWith match_s id x (op <$> y)
 〈naturality-r〉
 = selectWith match_s op x y

-}

-- * Misc

-- | Codiagonal
nabla :: Either a a -> a
nabla = either id id