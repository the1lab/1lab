---
description: |
  Reflection helpers for lists.
---
<!--
```agda
open import 1Lab.Reflection
open import 1Lab.Prelude hiding (absurd)

open import Data.List.Membership
open import Data.List.Base

open import Meta.Foldable
```
-->

```agda
module 1Lab.Reflection.List where
```

# Reflection utilities for lists

The following patterns are useful.

```agda
pattern `List `A = def (quote List) (unknown h∷ `A v∷ [])

pattern _`∷_ `x `xs = con (quote List._∷_) (unknown h∷ unknown h∷ `x v∷ `xs v∷ [])
pattern `[] = con (quote List.[]) (unknown h∷ unknown h∷ [])

pattern _`∷?_ `x `xs = con (quote List._∷_) (`x v∷ `xs v∷ [])
pattern `[]? = con (quote List.[]) []
```

We can quote lists of terms to get a quoted list, and we can
unquote terms to lists of terms, so long as the spine of the list
can be fully reduced.

```agda
quoteList : List Term → Term
quoteList = foldr _`∷_ `[]

{-# TERMINATING #-}
unquoteList : Term → TC (List Term)
unquoteList `xs =
  reduce `xs >>= λ where
    `[] → pure []
    (`x `∷ `xs) → `x ∷_ <$> unquoteList `xs
    (meta m _) → block-on-meta m
    `xs → typeError [ "unquoteList: can't unquote " , termErr `xs , " because it cannot be reduced to whnf." ]
```

We also provide patterns for list membership.

```agda
pattern _`∈ₗ_ `x `xs = def (quote _∈ₗ_) (unknown h∷ unknown h∷ `x v∷ `xs v∷ [])

pattern `here `p = con (quote _∈ₗ_.here) (unknown h∷ unknown h∷ unknown h∷ unknown h∷ `p v∷ [])
pattern `there `mem = con (quote _∈ₗ_.there) (unknown h∷ unknown h∷ unknown h∷ unknown h∷ `mem v∷ [])

pattern `here? `p = con (quote _∈ₗ_.here) (`p v∷ [])
pattern `there? `mem = con (quote _∈ₗ_.there) (`mem v∷ [])
```

## Proof automation for unique membership

Writing proofs that `is-contr (x ∈ₗ xs)` is a common but tedious task,
so we provide some macros for constructing them.

Our first helper function walks down a list, searching for an element
while accumulating a term for the proof that the element is in the list,
as well as patterns for matching that element and an absurd pattern.

```agda
private
  find-member-with
    : (`x : Term) (`xs : Term) (spine : List Term)
    → Term → Pattern → Pattern
    → TC (Term × Pattern × Pattern × List Term)
  find-member-with `x `xs [] `mem `found `not-found =
    typeError [ "has-member: could not find " , termErr `x , " in " , termErr `xs ]
  find-member-with `x `xs (`y ∷ spine) `mem `found `not-found =
    unifies? `x `y >>= λ where
      true → pure (`mem , `found , `not-found , spine)
      false →
        find-member-with `x `xs spine (`there `mem) (`there? `found) (`there? `not-found)
```

Our second helper also iterates through the list, but instead constructs
absurd clauses for each element.

```agda
private
  refute-member-with
    : (`x : Term) (`xs : Term) (spine : List Term)
    → Pattern → List Clause
    → List Clause
  refute-member-with `x `xs [] `not-found clauses = clauses
  refute-member-with `x `xs (`y ∷ spine) `not-found clauses =
    let `not-found-clause = absurd-clause (("_" , argN (`x `∈ₗ `xs)) ∷ []) (`not-found v∷ [])
    in refute-member-with `x `xs spine (`there? `not-found) (`not-found-clause ∷ clauses)

```

Our macro then calls these two helpers in sequence, and packages
the results into a `contr`{.Agda}.

```agda
  unique-member-worker
    : ∀ {ℓ} {A : Type ℓ}
    → (x : A) (xs : List A)
    → Term
    → TC ⊤
  unique-member-worker x xs hole = do
    `x ← quoteTC x
    spine ← traverse quoteTC xs
    let `xs = quoteList spine
    (`mem , `found , `not-found , rest) ←
          find-member-with `x `xs spine
            (`here (con (quote reflᵢ) []))
            (`here? (con (quote reflᵢ) []))
            (`here? (absurd 0))
    let clauses =
          refute-member-with `x `xs rest
            (`there? `not-found)
            (clause [] (`found v∷ []) (def (quote refl) []) ∷ [])
    unify hole (con (quote contr) (`mem v∷ pat-lam clauses [] v∷ []))

unique-member!
  : ∀ {ℓ} {A : Type ℓ}
  → {x : A} {xs : List A}
  → {@(tactic unique-member-worker x xs) mem : is-contr (x ∈ₗ xs)}
  → is-contr (x ∈ₗ xs)
unique-member! {mem = mem} = mem
```

We also get a macros for proving that an element is either in or not in a list en-passant.

```agda
private
  member-worker
    : ∀ {ℓ} {A : Type ℓ}
    → (x : A) (xs : List A)
    → Term
    → TC ⊤
  member-worker x xs hole = do
    `x ← quoteTC x
    spine ← traverse quoteTC xs
    let `xs = quoteList spine
    (`mem , _ , _ , _) ←
          find-member-with `x `xs spine
            (`here (con (quote reflᵢ) []))
            (`here? (con (quote reflᵢ) []))
            (`here? (absurd 0))
    unify hole `mem

  not-member-worker
    : ∀ {ℓ} {A : Type ℓ}
    → (x : A) (xs : List A)
    → Term
    → TC ⊤
  not-member-worker x xs hole = do
    `x ← quoteTC x
    `xs ← traverse quoteTC xs
    let clauses = refute-member-with `x (quoteList `xs) `xs (`here? (absurd 0)) []
    unify hole (pat-lam clauses [])

member!
  : ∀ {ℓ} {A : Type ℓ}
  → {x : A} {xs : List A}
  → {@(tactic member-worker x xs) mem : x ∈ xs}
  → x ∈ xs
member! {mem = mem} = mem

not-member!
  : ∀ {ℓ} {A : Type ℓ}
  → {x : A} {xs : List A}
  → {@(tactic not-member-worker x xs) not-mem : x ∉ xs}
  → x ∉ xs
not-member! {not-mem = not-mem} = not-mem
```

## Examples

```agda
private
  member-example : true ∈ [ false , true , false , true , false ]L
  member-example = member!
  not-member-example : true ∉ [ false , false , false ]L
  not-member-example = not-member!

  unique-member-example : is-contr (true ∈ [ false , true , false , false ]L)
  unique-member-example = unique-member!
```
