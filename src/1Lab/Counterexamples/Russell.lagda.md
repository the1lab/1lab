---
description: |
  We formalise Russell's paradox: It is impossible for the collection of
  all types to be a type.
---
<!--
```agda
{-# OPTIONS --type-in-type #-}
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Counterexamples.Russell where
```

# Russell's paradox {defines="russell's-paradox"}

This page reproduces [Russell's paradox] from naïve set theory using an
inductive type of `Type`{.Agda}-indexed trees. By default, Agda places
the type `Type₀` in `Type₁`, meaning the definition of `V`{.Agda} below
would not be accepted. The `--type-in-type` flag disables this check,
meaning the definition goes through.

[Russell's paradox]: https://en.wikipedia.org/wiki/Russell%27s_paradox

```agda
data V : Type where
  set : (A : Type) → (A → V) → V
```

The names `V`{.Agda} and `set`{.Agda} are meant to evoke the [cumulative
hierarchy] of sets. A ZF set is merely a particular type of tree, so we
can represent the cumulative hierarchy as a particular type of trees -
one where the branching factor of a node is given by a type `A`.

[cumulative hierarchy]: https://en.wikipedia.org/wiki/Von_Neumann_universe

We define the membership predicate `_∈_`{.Agda} by pattern matching,
using the [[path type|path]] `_≡_`{.Agda}:

```agda
_∈_ : V → V → Type
x ∈ set A f = Σ A λ i → f i ≡ x
```

A set `x` is an element of some other set if there exists an element of
the index type which the indexing function maps to `x`. As an example,
we have the empty set:

```agda
Ø : V
Ø = set ⊥ λ ()

X∉Ø : {X : V} → ¬ X ∈ Ø
X∉Ø ()
```

Given the `_∈_`{.Agda} predicate, and the fact that we can quantify over
all of `V` and still stay in `Type₀`, we can make _the set of all sets
that do not contain themselves_:

```agda
R : V
R = set (Σ _ λ x → ¬ x ∈ x) fst
```

If `X` is an element of `R`, then it does not contain itself:

```agda
X∈R→X∉X : {X : V} → X ∈ R → ¬ X ∈ X
X∈R→X∉X ((I , I∉I) , prf) elem =
  let I∈I : I ∈ I
      I∈I = subst (λ x → x ∈ x) (sym prf) elem
  in I∉I I∈I
```

Using a diagonal argument, we can show that R does not contain itself:

```agda
R∉R : ¬ R ∈ R
R∉R R∈R = X∈R→X∉X R∈R R∈R
```

And every set that doesn't contain itself is an element of `R`:

```agda
X∉X→X∈R : {X : V} → ¬ X ∈ X → X ∈ R
X∉X→X∈R X∉X = (_ , X∉X) , refl
```

This leads to a contradiction.

```agda
Russell : ⊥
Russell = R∉R (X∉X→X∈R R∉R)
```
