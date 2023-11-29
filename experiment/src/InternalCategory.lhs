> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE StandaloneKindSignatures #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE FunctionalDependencies #-}
> module InternalCategory where

> import Data.Type.Equality
> import Data.Kind (Type, Constraint)
  
A small category is a category \\(C\\) such that the collection of its objects can be a set \\(\mathrm{Ob}(C) : \mathrm{\mathbf{Set}}\\),
and the collection of (the sum of) its all arrows, regardless of its source and target, is a set \\(\mathrm{Mor}(C) : \mathrm{\mathbf{Set}\\).

(When using an appropriate set theory,) the category \\(C\\) can be completely described using sets \\(\mathrm{Ob}(C), \mathrm{Mor}(C)\\).

* Two sets \\(X = \mathrm{Ob}(C), A = \mathrm{Mor}(C)\\)
* Morphisms \\(\mathrm{src} : A \to X\\) and \\(\mathrm{dst} : A \to X\\), which gives a "source" object and "target" object of an arrow, respectively.
* Morphism \\(\mathrm{id} : X \to A), which corresponds identity morphisms for each object (recall that objects are elements of \\(X\\).)
* Morphism \\((\circ) : A \otimes A \to A ), where \\(A \otimes A\\) is the pullback along \\(\mathrm{src}\\) and \\(\mathrm{dst}\\)

  \\[
    A \otimes A = \lbrace (f,g) \mid \mathrm{src}(f) = \mathrm{dst}(g) \rbrace.
  \\]

  \\((\circ)\\) represents the composition of morphisms in \\(C\\).

This definition of small categories can be translated to Haskell using "dependent types."
The scare quote is there because it's emulated using the singleton type hack.

For example, instead of using the set two values `Bool`, we use a singleton type indexed by the values of `Bool`.

> data SBool (x :: Bool) where
>   SFalse :: SBool False
>   STrue  :: SBool True
>
> instance TestEquality SBool where
>   testEquality SFalse SFalse = Just Refl
>   testEquality STrue  STrue  = Just Refl
>   testEquality _ _ = Nothing

We use this singleton-ized datatype as a representation of the set of objects.
Additionally, instead of representing the set of arrows as a single type, let them be a family of fibers of \\(A\\),
along its source and destination objects (\\(\mathrm{src}(f), \mathrm{dst}(f)\\). 

> type Category :: (k -> Type) -> (k -> k -> Type) -> Constraint
> class (TestEquality ob) => Category ob arr | arr -> ob where
>   src :: arr x y -> ob x
>   dst :: arr x y -> ob y
>   identity :: ob x -> arr x x
>   compose :: arr y z -> arr x y -> arr x z

> data Implication (x :: Bool) (y :: Bool) where
>   Imp00 :: Implication False False
>   Imp01 :: Implication False True
>   Imp11 :: Implication True  True

> instance Category SBool Implication where
>   src Imp00 = SFalse
>   src Imp01 = SFalse
>   src Imp11 = STrue
>   dst Imp00 = SFalse
>   dst Imp01 = STrue
>   dst Imp11 = STrue
>   identity SFalse = Imp00
>   identity STrue  = Imp11
>   compose Imp00 Imp00 = Imp00
>   compose Imp01 Imp00 = Imp01
>   compose Imp11 Imp01 = Imp01
>   compose Imp11 Imp11 = Imp11

--------

What will happen if you do the same thing on the [categories of containers(pdf)](https://www.cs.le.ac.uk/people/ma139/docs/thesis.pdf)?