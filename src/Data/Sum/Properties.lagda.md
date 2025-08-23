<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.Function.Embedding
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Sum.Base

open import Meta.Invariant
```
-->

```agda
module Data.Sum.Properties where
```

# Properties of sum types

<!--
```agda
private variable
  a b c d : Level
  A B C D : Type a
```
-->

Many useful properties of [[sum types]] will fall out of characterising
their *path spaces*. We start by defining a reflexive family of codes
for paths in `A ⊎ B`: between elements in the same component, a code is
simply a path in the corresponding type, while there are no codes between
elements in different components.

```agda
module ⊎Path {a b} {A : Type a} {B : Type b} where
  Code : A ⊎ B → A ⊎ B → Type (level-of A ⊔ level-of B)
  Code (inl x) (inl y) = Lift (level-of B) (x ≡ y)
  Code (inl x) (inr y) = Lift _ ⊥
  Code (inr x) (inl y) = Lift _ ⊥
  Code (inr x) (inr y) = Lift (level-of A) (x ≡ y)

  Code-refl : (x : A ⊎ B) → Code x x
  Code-refl (inl x) = lift refl
  Code-refl (inr x) = lift refl
```

Given a `Code`{.Agda} for a path in `A ⊎ B`, we can turn it into a
legitimate path by `ap`{.Agda}plying the corresponding constructor.
Agda automatically lets us ignore the cases where the `Code`{.Agda}
computes to `the empty type`{.Agda ident=⊥}.

```agda
  decode : {x y : A ⊎ B} → Code x y → x ≡ y
  decode {x = inl x} {y = inl y} code = ap inl (lower code)
  decode {x = inr x} {y = inr y} code = ap inr (lower code)
```

This lets us show that `Code`{.Agda} is an [[identity system]], so
that we get an equivalence between codes and paths.

```agda
  ids : is-identity-system Code Code-refl
  ids .to-path = decode
  ids .to-path-over {inl x} {inl y} (lift p) i = lift λ j → p (i ∧ j)
  ids .to-path-over {inr x} {inr y} (lift p) i = lift λ j → p (i ∧ j)

  Code≃Path : {x y : A ⊎ B} → (x ≡ y) ≃ Code x y
  Code≃Path = identity-system-gives-path ids e⁻¹
```

## Injectivity and disjointness of constructors

A first very useful consequence is that the constructors `inl`{.Agda}
and `inr`{.Agda} are *injective* and *disjoint*:

```agda
open ⊎Path

inl-inj : {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
inl-inj = lower ∘ Code≃Path .fst

inr-inj : {A : Type b} {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
inr-inj = lower ∘ Code≃Path .fst

inl≠inr : {A : Type a} {B : Type b} {x : A} {y : B} → ¬ inl x ≡ inr y
inl≠inr = lower ∘ Code≃Path .fst

inr≠inl : {A : Type a} {B : Type b} {x : A} {y : B} → ¬ inr x ≡ inl y
inr≠inl = lower ∘ Code≃Path .fst
```

In fact they are even [[embeddings]]:

```agda
inl-is-embedding : is-embedding (inl {A = A} {B})
inl-is-embedding = cancellable→embedding (Code≃Path ∙e Lift-≃)

inr-is-embedding : is-embedding (inr {A = A} {B})
inr-is-embedding = cancellable→embedding (Code≃Path ∙e Lift-≃)
```

## Closure under h-levels

As another consequence, if $A$ and $B$ are $n$-types for $n \ge 2$,
then so is their coproduct.

We first observe that `Code`{.Agda} is a family of $(n-1)$-types, which
is automatic in every case using instance search:

```agda
Code-is-hlevel : {x y : A ⊎ B} {n : Nat}
               → ⦃ H-Level A (2 + n) ⦄
               → ⦃ H-Level B (2 + n) ⦄
               → is-hlevel (Code x y) (suc n)
Code-is-hlevel {x = inl x} {inl y} {n} = hlevel (suc n)
Code-is-hlevel {x = inr x} {inr y} {n} = hlevel (suc n)
Code-is-hlevel {x = inl x} {inr y} {n} = hlevel (suc n)
Code-is-hlevel {x = inr x} {inl y} {n} = hlevel (suc n)
```

Thus, so are paths in `A ⊎ B`, which concludes the proof.

```agda
⊎-is-hlevel : (n : Nat)
            → ⦃ H-Level A (2 + n) ⦄
            → ⦃ H-Level B (2 + n) ⦄
            → is-hlevel (A ⊎ B) (2 + n)
⊎-is-hlevel {A = A} {B = B} n x y =
  Equiv→is-hlevel (1 + n) Code≃Path Code-is-hlevel
```

<!--
```agda
instance
  H-Level-⊎ : ∀ {n} ⦃ _ : 2 ≤ n ⦄ ⦃ _ : H-Level A n ⦄ ⦃ _ : H-Level B n ⦄ → H-Level (A ⊎ B) n
  H-Level-⊎ {n = suc (suc n)} ⦃ s≤s (s≤s p) ⦄ = hlevel-instance $
    ⊎-is-hlevel _
```
-->

Note that, in general, being a [[proposition]] and being [[contractible]]
is not preserved under coproducts. Consider the type `⊤ ⊎ ⊤`: this
is a coproduct of contractible types (hence propositions) that is not
itself a proposition. However, the coproduct of _disjoint_ propositions
is a proposition:

```agda
disjoint-⊎-is-prop
  : is-prop A → is-prop B → ¬ (A × B)
  → is-prop (A ⊎ B)
disjoint-⊎-is-prop Ap Bp notab (inl x) (inl y) = ap inl (Ap x y)
disjoint-⊎-is-prop Ap Bp notab (inl x) (inr y) = absurd (notab (x , y))
disjoint-⊎-is-prop Ap Bp notab (inr x) (inl y) = absurd (notab (y , x))
disjoint-⊎-is-prop Ap Bp notab (inr x) (inr y) = ap inr (Bp x y)
```

## Discreteness

If `A` and `B` are [[discrete]], then so is `A ⊎ B`.

```agda
instance
  Discrete-⊎ : ⦃ _ : Discrete A ⦄ ⦃ _ : Discrete B ⦄ → Discrete (A ⊎ B)
  Discrete-⊎ .decide (inl x) (inl y) = invmap (ap inl) inl-inj (x ≡? y)
  Discrete-⊎ .decide (inl x) (inr y) = no inl≠inr
  Discrete-⊎ .decide (inr x) (inl y) = no inr≠inl
  Discrete-⊎ .decide (inr x) (inr y) = invmap (ap inr) inr-inj (x ≡? y)
```
