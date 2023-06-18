{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Concrete.Category where

import Concrete.Span

import Data.Kind

type family Ob (cat :: k -> k -> Type) :: k -> Type

type Category :: (k -> k -> Type) -> Constraint
class (Span (Ob cat) (Ob cat) cat) => Category cat where
    ident :: Ob cat a -> cat a a
    compose :: cat a b -> cat b c -> cat a c

infixr 2 >>>

(>>>) :: (Category hom) => hom a b -> hom b c -> hom a c
(>>>) = compose

infixr 2 <<<

(<<<) :: (Category hom) => hom b c -> hom a b -> hom a c
(<<<) = flip compose