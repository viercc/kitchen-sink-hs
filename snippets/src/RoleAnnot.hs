{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}
module RoleAnnot where

type role Foo_P phantom
data Foo_P a = Foo_P

type role Foo_R representational
data Foo_R a = Foo_R

type role Foo_N nominal
data Foo_N a = Foo_N



type role Bar_P phantom
newtype Bar_P a = Bar_P ()

type role Bar_R representational
newtype Bar_R a = Bar_R a

type role Bar_N nominal
newtype Bar_N a = Bar_N (forall f. f a -> f Int)