# Context

Recently, I read discussions started by @tysonzero (u/Tysonzero @ reddit), revolving around
the problem with `-XFlexibleInstance`.
When we use `-XFlexibleInstances`, a program can be silently incoherent
even when `-Worphans` is enabled and a programmer gave no annotations to relax
ambiguous instance resolution (`{-# Overlappable #-}`, etc.)

https://www.reddit.com/r/haskell/comments/dcflzu/flexibleinstances_can_cause_silent_instance/

https://www.reddit.com/r/haskell/comments/dbk09n/worphans_is_overly_lenient/

Of course, without `-XFlexibleInstances`, such program always warned by `-Worphans` option.
This note thinks about how `-Worphans` can be more restrictive to prevent such a case.

# Preparation

A type T is:

* Type constructor `A`, `B`, `C`, ...
* Type variable `x`, `y`, `z`, ...
* Application (T1 T2)

Define these concepts as we usually do.

* Substitution σ = { T/x, U/y, ... }
* Applying substitution T{U1/x, U2/y, ...}

  * Example: (A (x y) x){(B y)/x} = A (B y y) (B y)

* General-Special order ≤

  * T ≤ U  ⇔  There exists σ s.t. Tσ = U

  * Example: x ≤ f y ≤ A z y ≤ A y y ≤ A B B

* Unification (least upper bound of ≤)



# Definition

For a type constructor `A` and type `T`, `d(A,T)` (reads A dominates T)
means:

* d(A, A) always hold
* d(A, T1 T2) hold if either one of the following hold:
  * d(A, T1)
  * T1 does not contain type variable &&
    d(A, T2)
* A dominates nothing other than above

Alternatively, in Haskell,

```haskell
data Type = TyCon String | TyVar String | App Type Type

hasNoTyVar :: Type -> Bool
hasNoTyVar = ...

d :: String -> Type -> Bool
d con (TyCon con') = con == con'
d _   (TyVar _)    = False
d con (App t1 t2)  = d con t1 || hasNoTyVar t1 && d con t2
```

Lemma. d(A,T) ⇒ T contains A.

# Preventing incoherence

The idea is, `instance C T` is not orphan ⇔ `C` is defined in this module or
for some `A` defined in this module, d(A,T).

## Examples.

```Haskell
module Foo where
  class C a

module Foo where
  import Foo

  data E
  data F a

  -- Non-orphans in vanilla GHC is still non-orphan 
  instance C E
  instance C (F a)
  
  instance C (f E)       -- orphan
  instance C (E -> a)
  instance C (Bool -> E)
  instance C (a -> E)    -- orphan
  instance C (F a -> a)
  instance C (a -> F a)  -- orphan
```

## Properties of this fix

### It prevents the problem discussed

This definition prevents incoherent instances being used silently.

Predicate d(-,-) has the following property:

[Theorem] Safety of d(-,-).

> For all A, B, T, U, suppose both d(A,T) and d(B,U) holds. Then,
> T and U unify (∃V, T ≤ V and U ≤ V) implies (U contains A) or (T contains B).

Proof.
  
  If A = B, the theorem trivially holds. Suppose A ≠ B.

  If T=A, then U=A since T and U unifies. But ¬d(B,U=A) since A ≠ B. So T≠A.
  Similarly, U≠B.

  To d(A,T) and d(B,U) to hold, it must be T = T1 T2 and U = U1 U2.

  there are four cases of reason d(A,T) and d(B,U) hold.

  1. d(A,T1) and d(B,U1) holds.

     If T and U unify, also T1 and U1 do.
     Thus, by induction, either (U1 contains A) or (T1 contains B) hold.
     Hence the claim holds.

  2. d(A,T2) and d(B,U2) holds.

     If T and U unify, also T2 and U2 do.
     Thus, by induction, either (U2 contains A) or (T2 contains B) hold.
     Hence the claim holds.

  3. T1 does not contain type variable and d(B,U1) holds.

     If T and U unify, also T1 and U1 do.
     Since T1 does not contain type variable, U1 ≤ unify(T1, U1) = T1.
     U1 contains B, thus also occurs in T1. The claim holds.

  4. U1 does not contain type variable and d(A,T1) holds.

     Similarly to 3., U1 contains A thus the claim holds.

Suppose a module `Foo` defines `A` and declares `instance C T` s.t. d(A,T).
Also, a module `Bar` defines `B` and declares `instance C U` s.t. d(B,U).
If these instances overlap, in other words T and U unify, then either (T contains B) or (U contains A).
That means module `Foo` depends `Bar` or other way around. For a type V both T ≤ V and U ≤ V,
if both of instances from `Foo` and `Bar` is used somewhere in the program, GHC can reject at least one of
them. For example, when `Foo` depends `Bar` (because T contains B), `instance C U` always
exists in the scope when `instance C T` is in the scope. Trying to resolve a constraint `C V` raises error.


### It is maximal

Another "nice" point about this d(-,-) predicate is, it is *maximal* in the sense
you can allow no extra pair (A,T) to maintain the above property.

Assume a pair (A,T), which does not satisfy d(A,T), is considered non-orphan.

Let x be a variable occuring in T, occuring at leftmost position.
Starting from T, replace every occurence of A with a fresh variable y,
then replace every occurence of x with newly created type costructor B.
Let U be the result of this transformation.

It can be shown that d(B,U) and U does not contain A.
This allows `instance C U` be declared without warning, in the new module
defining B, which does not depend on the module which owns A.

Since T and U unifies (V = U{A/y} = T{B/x}), it can break coherence silently.

### Allows all Haskell2010 instances

This method keeps decision for every instances which does not require
`-XFlexibleInstances`.

Pure Haskell2010 instances are strictly in form of the following.

```haskell
instance C (TC tv1 tv2 ... tvn)
```

The current decision for what is considered orphans do not change for them.

### This method is not unique to the requirement

There is another notion of dominance which satisfies the goodies
said above.

* Is safe
* Is maximal
* Is extension of standard

Observe that, (ignoring ill-kindedness which is not relevant,)

```
d'(A,T) = d(A, reverse(T)) where
  reverse(T1 T2) = reverse(T2) reverse(T1)
  reverse(x)     = x
```

is also a safe and maximal criteria, but not an extension of standard.
Modifying d'(A,T) a bit, we can construct d''(-,-) which is still
safe and maximal, and also is an extension of standard.

```
leftmost(T) = T            if T is constructor or variable
            = leftmost(T1) if T = T1 T2

d''(A,T) =  leftmost(T) == A
         || leftmost(T) is not variable &&
            d'(A,T)
```

There can be many, many variant of d(-,-).

# Extending dominance to MPTCs

## Definition

This method can be extended to cover MPTCs.

For example, consider a type class with three arguments.

```
class C a b c
```

We can define d(A,T1,T2,T3) like this.

```
d(A,T1,T2,T3) =
     d(A,T1)
  || T1 does not contain type variable && d(A,T2)
  || T1 and T2 does not contain type variable && d(A,T3)
```

Then, whether `instance C U1 U2 U3` is orphan or not is
judged by d(A,U1,U2,U3) for each A defined by the module
that instance lives.

But, there is a freedom of choice: you can reorder the argument
of `C` when passing them to `d`, as long as it is consistent.
Judging by d(A,U3,U1,U2) is also OK.

## It fails to comply with current behavior

Unlike non-MPTCs, this method **does not comply** with
current `-XMultiParamTypeClasses -XNoFlexibleInstances`.

``` haskell
module Foo where
  class C a b

module Bar where
  import Foo
  
  data F a
  
  -- Currently, these instances are allowed.
  -- But the proposed change does not allow both.
  -- Depending an order of parameters, only one of them
  -- are allowed.
  instance C (F a) [b]
  instance C [a]   (F b)
  
  -- Why? Suppose the order is left-to-right.
  --   C T U is not orphan ⇔ d(F,T,U)
  -- Then, this method judges
  -- 
  -- instance C (F a) [b]   -- (1):OK
  -- instance C [a]   (F b) -- (2):Orphan
  -- 
  -- This is, because in another module Bar, there can be
  --
  -- data Bar = Bar
  -- instance C [Bar] b     -- (3):OK
  --
  -- Which may overlap to the instance (2).
```

## On FunDeps

I'm not sure how it should be for FunDeps. I can give a
speculation like this:

* A class with FunDep like `C a b c | a -> b` can have one or more set of
  its arguments which completely determines all of other arguments.

  * `C a b | a -> b`   => {a}
  * `C a b c | a -> b` => {a,c}
  * `C a b | a -> b, b -> a` => {a} or {b}
  * `C a b c | a b -> c, b c -> a` => {a,b} or {b,c}

  Let me call such set of arguments a covering of C.

* How about this implementation:

  For each minimal covering W1,W2,... of C, using some previously fixed
  ordering on W1, W2, ..., we can think W1, W2, ... be a tuple (of arguments)
  instead of a set.

  ```
  C(T1,T2,...) is not orphan ⇔
    ∀W=(i,j,...) ∈ {W | W is a covering of C}, d(A, Ti, Tj, ...)
  ```

  For example,

  * `class C a b | a -> b`
    * `instance C T1 T2` is not orphan ⇔ d(A,T1)
  * `class C a b | a -> b, b -> a`
    * `instance C T1 T2` is not orphan ⇔ d(A,T1) && d(A,T2)
  * `class C a b c | a -> b`
    * There is a freedom of choice among:
      * `instance C T1 T2 T3` is not orphan ⇔ d(A,T1,T3)
      * `instance C T1 T2 T3` is not orphan ⇔ d(A,T3,T1)

# Issues not yet adressed

* Isn't this overengineering?
* Is the speculated implementation for FunDeps correct?
* There have to be some arbitrary choice if this is to be
  implemented.
  * Which d(-,-) is chosen? I think there is no reason to
    choose somthing like d''(-,-), but maybe maybe.
  * How arguments of a MPTC are ordered?
    * Should there be a canonical order, or make it customizable?

# Comparison to other fixes

( _Emphasized_ part is my augmentation. )

## (A) Fix given by @ekmett

@ekmett gave simpler fix in a comment to PR. I would restate it as:

* _`instance C ...` in the module which "owns" the type class C is not orphan._
* `instance C T` is not orphan if leftmost(T) is
  a type constructor is "owned" by the same module.
* `instance C T1 T2 ... Tn` is not orphan if
  all of the leftmost(T1), leftmost(T2), ..., leftmost(Tn) are
  type constructors and at least one of them is owned by the same module.

## (B) Fix given by the proposal

Link: https://github.com/tysonzero/ghc-proposals/blob/patch-2/proposals/0000-prevent-incoherent-instances.rst

I would restate it as:

* For each declaration `class C a1 a2 ... an`, a subset of its arguments
  is associated with the class.
  It can be specified by a programmer using `Refine` pragma, or it's a default.

* For each declaration `[no]instance C ...`, a subset of type variables
  occuring in the head of declaration is associated with the instance.
  It can be specified by a programmer using `Refine` pragma, or it's a default.

* A declaration `instance C T1 T2 ... Tn` in a module _which does not "owns"_ `C`
  is considered non-orphan only when either one of the following conditions met:

  * Let U1, U2, ... be the arguments of `C` which corresponds to the arguments in
    the associated set of arguments for the class (`Refine` pragma associated to
    the `class C` declaration). leftmost(U1), leftmost(U2), ... must be type
    constructors and at least one of them must be owned by the same module.
    
    * _This condition is used only when no other instances overlap to it._

  * _If there is a [no]instance which can be specialized to the instance being declared,_
    _let's call that preexisting [no]instance be the parent._ There is a substitution σ which
    makes the head of the parent into the head of the instance being declared.
    For each variable x in the set associated to the parent, let Tx = xσ be the type
    which substitutes x for the instance being declared. All of leftmost(Tx) must be
    type constructors and at least one of them must be owned by the same module.
    
    * _There must be no other [no]instances overlapping to the instance being declared._

(I didn't include the part for changing behavior of anything other than what warning is emitted.
I'm against all of hard breakages in the proposal, because they will break existing code which is
explicitly annotated by the programmer, on their own responsibility.)

## Comparison

The method this note proposes is referred as (C).

Summary:

* Safe: Not sure for (B). Both (A) and (C) can ensure safety. 
* Permissive: (A) < (B), (C) is not comparable to both.
* Flexibility: (A) < (C) < (B)
* Added complexity: (B) > (C) > (A)
* Implementation difficulty (my guess): (B) >> (C) > (A)
* Intuitive (for me): (B) < (C) < (A)

### Safe

The "safety" this comparison cares is exactly whether
silent, unintentional incoherence occurs.

From me, it is obvious that (A) keeps us from incoherence.
This note showed (C) is also safe -- hope I didn't miss something!

### Permissive

(B) can express the restriction of (A), but different restriction
can be put on class-by-class basis.

There is an instance (A) or (B) would accept but (C) would not accept.
Also, there is an instance (C) would accept but (A) or (B) would not.

``` haskell
module Foo where
  class C a b
    {-# Refine a b #-}

module Bar where
  import Foo
  
  import Middleware.Specific.Types (M)
  
  data F x
  
  instance C (F x) [y]   -- All of (A) (B) (C) accept
  instance C [x] (F y)   -- (A) (B) only
  instance C (F x) y     -- (C) only, but (B) can be customized to allow it
  instance C x (F y)     -- Nothing accept, but (B) can be customized to allow it
  instance C [F x] [F x] -- (C) only, but (B) can be customized to allow it
  instance C (M (F x)) (M (F x)) -- (C) only
```

**Disclaimer:** How much it is permissive relies greatly on
how many times everyone's actually used codes affected.
**I have no idea.** Probably more experienced people and empirical data
(like samples taken from Hackage) are needed.

### Flexibility

(A) has no moving parts.

(B) has many moving parts to cover various situations.

(C) *possibly* includes the annotation for MPTCs.

### Added complexity

(A) does not require the language to be extended.

(C) *possibly* includes the annotation for MPTCs.
The main concept of d(A,T) is a bit deeper than (A),
but once it is defined nothing needed to be changed further.

(B) adds { `noinstance`, `Refine` pragma } as new syntactic element.
New orphans checker need to know about `[no]instance` existing in the scope,
and perform almost complete instance selection algorithm.
I think this is far, far more complex than (A) or (C).

### Implementation difficulty

Well, I have no experience in touching GHC code so I may missing the point,
but isn't (B) the hardest?

### Intuitive

Mere subjective evalutaion. (B) < (C) < (A).
