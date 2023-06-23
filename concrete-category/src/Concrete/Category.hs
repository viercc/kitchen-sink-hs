{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Category where

import Concrete.Span

import Data.Kind

type Category :: (k -> k -> Type) -> Constraint
class (Span cat, Dom cat ~ Cod cat) => Category (cat :: k -> k -> Type) where
    ident :: Ob cat a -> cat a a
    compose :: cat a b -> cat b c -> cat a c

type Ob cat = Dom cat

infixr 2 >>>

(>>>) :: (Category hom) => hom a b -> hom b c -> hom a c
(>>>) = compose

infixr 2 <<<

(<<<) :: (Category hom) => hom b c -> hom a b -> hom a c
(<<<) = flip compose

instance Category (->) where
    ident _ = id
    compose x y = y . x
