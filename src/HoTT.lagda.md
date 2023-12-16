<!--
```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel

open import Data.Wellfounded.W
open import Data.Nat
open import Data.Dec
open import Data.Sum
open import Data.Fin
```
-->

```agda
module HoTT where
```

# The HoTT Book?

While the 1Lab has not been consciously designed as a project to
formalise the HoTT book, in the course of our explorations into
formalised univalent mathematics, we have formalised a _considerable_
subset of the first part, and most of chapter 9. The vast majority of
the 1Lab is material that was _not_ covered in the HoTT book.

# Part 1 Foundations

## Chapter 2 Homotopy type theory

### 2.1 Types are higher groupoids

### 2.2 Functions are functors

### 2.3 Type families are fibrations

### 2.4 Homotopies and equivalences

### 2.7 Cartesian product types

### 2.9 Π-types and function extensionality

### 2.10 Universes and univalence

### 2.11 Identity type

### 2.12 Coproducts

## Chapter 3 Sets and Logic

### 3.1 Sets and n-types

### 3.3 Mere propositions

### 3.5 Subsets and propositional resizing

### 3.7 Propositional truncation

<!--
```agda
_ = ∥_∥
_ = ∃
```
-->

The type itself is defined as a higher-inductive type `∥_∥`{.Agda}. We
also define `∃`{.Agda} as a shorthand for the truncation of `Σ`{.Agda}.

### 3.9 The principle of unique choice

### 3.11 Contractibility

### Exercises

<!--
```agda
_ = equiv→is-hlevel
_ = ⊎-is-hlevel
_ = Σ-is-hlevel
_ = is-contr-if-inhabited→is-prop
_ = is-prop∙→is-contr
_ = H-Level-Dec
_ = disjoint-⊎-is-prop
_ = ℕ-well-ordered
_ = is-prop≃equiv∥-∥
_ = Finite-choice
```
-->

* Exercise 3.1: `equiv→is-hlevel`{.Agda}
* Exercise 3.2: `⊎-is-hlevel`{.Agda}
* Exercise 3.3: `Σ-is-hlevel`{.Agda}
* Exercise 3.5: `is-contr-if-inhabited→is-prop`{.Agda}, `is-prop∙→is-contr`{.Agda}
* Exercise 3.6: `H-Level-Dec`{.Agda}
* Exercise 3.7: `disjoint-⊎-is-prop`{.Agda}
* Exercise 3.19: `ℕ-well-ordered`{.Agda}
* Exercise 3.21: `is-prop≃equiv∥-∥`{.Agda}
* Exercise 3.22: `Finite-choice`{.Agda}

## Chapter 4 Equivalences

### 4.2 Half adjoint equivalences

### 4.3 Bi-invertible maps

### 4.4 Contractible fibres

:::{.note}
This is our "default" definition of equivalence, but we
generally use it through the interface of half-adjoint equivalences.
:::

### 4.6 Surjections and embeddings

### 4.8 The object classifier

## Chapter 5 Induction

<!--
```agda
_ = W
```
-->

### 5.3 W-types

* W-types: `W`{.Agda}

### 5.4 Inductive types are initial algebras

## Chapter 6 Higher inductive types

### 6.2 Induction principles and dependent paths

### 6.3 The interval

::: note
This is the higher inductive type `[0,1]`{.Agda}, _not_ the interval type
`I`{.Agda}.
:::

### 6.5 Circles and spheres

### 6.4 Circles and spheres

### 6.6 Cell complexes

### 6.9 Truncations

### 6.10 Quotients

### 6.11 Algebra

## Chapter 7 Homotopy n-types

### 7.1 Definition of n-types

### 7.2 Uniqueness of identity proofs and Hedberg's theorem

### 7.3 Truncations

### 7.5 Connectedness

# Part 2 Mathematics

## Chapter 8 Homotopy theory

The only non-trivial result worth mentioning from Chapter 8 is the
fundamental group of the circle.

### 8.1 π₁(S¹)

### 8.2 Connectedness of suspensions

### 8.6 The Freudenthal suspension theorem

## Chapter 9 Category theory

Since a vast majority of the 1Lab's mathematics consists of pure
category theory, or mathematics done with a very categorical
inclination, this is our most complete chapter.

### 9.1 Categories and precategories

### 9.2 Functors and transformations

### 9.3 Adjunctions

### 9.4 Equivalences

### 9.5 The Yoneda lemma

### 9.6 Strict categories

This chapter is mostly text.

### 9.7 Dagger categories

We do not have a type of dagger-categories, but note that we do have the
closely-related notion of [allegory].

[allegory]: Cat.Allegory.Base.html

### 9.8 The structure identity principle

### 9.9 The Rezk completion
