```agda
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import 1Lab.Data.Dec

module 1Lab.Data.Relation.Order where
```

# Order relations

This module characterises different types of binary relations, and, in
particular, ordering relations.

<!--
```
private variable
  ℓ ℓ' : Level
  A : Type ℓ
  R : A → A → Type ℓ'
```
-->

A relation is _reflexive_ if we have `R x x`, for any `x`:

```agda
isReflexive : (R : A → A → Type ℓ) → Type _
isReflexive R = {x : _} → R x x
```

A relation is _transitive_ if `R x y` and `R y z` implies `R x z`.

```agda
isTransitive : (R : A → A → Type ℓ) → Type _
isTransitive R = {x y z : _} → R x y → R y z → R x z
```

A **preorder** is a reflexive, transitive relation. Furthermore, we
impose that a preorder take value in propositions.

```agda
record isPreorder {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    reflexive     : isReflexive R
    transitive    : isTransitive R
    propositional : {x y : A} → isProp (R x y)
```

A **partial order** is a preorder which, in addition, is antisymmetric:

```agda
isAntiSymmetric : (R : A → A → Type ℓ) → Type _
isAntiSymmetric R = {x y : _} → R x y → R y x → x ≡ y

record isPartialOrder {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    preorder : isPreorder R
    antisym : isAntiSymmetric R

  open isPreorder preorder public
```
We say a relation is **trichotomous** for all `x,y` if exactly _one_ of `R x y`, `x ≡ y`, or `R y x` holds.
We define this in two parts: First we define what trichotomy means for 2 elements via `Tri`, then
`Trichotomous` in terms of `Tri`.
```agda
data Tri {A : Type ℓ} (R : A → A → Type ℓ') (x y : A) : Type (ℓ ⊔ ℓ') where
  lt : R x y       → (x ≡ y → ⊥) → (R y x → ⊥) → Tri R x y
  eq : (R x y → ⊥) → x ≡ y       → (R y x → ⊥) → Tri R x y
  gt : (R x y → ⊥) → (x ≡ y → ⊥) → R y x       → Tri R x y

isTrichotomous : {A : Type ℓ} → (R : A → A → Type ℓ') → Type (ℓ ⊔ ℓ')
isTrichotomous R = ∀ x y → Tri R x y
```

Trichotomy is a very powerful property, and we can derive a lot of useful
results from it!

To start, trichotomy immediately implies discreteness:
```agda
trichotomous-discrete : ∀ {A : Type ℓ} {R : A → A → Type ℓ'} → isTrichotomous R → Discrete A
trichotomous-discrete compare x y with compare x y
... | lt _ ¬x≡y _ = no ¬x≡y
... | eq _  x≡y _ = yes x≡y
... | gt _ ¬x≡y _ = no ¬x≡y
```

These results aren't particularly deep, but are useful nonetheless.
If `x` and `y` are trichotomous with respect to one another, then
we can flip everything around without consequence.
```agda
tri-sym : ∀ {x y} → Tri R x y → Tri R y x
tri-sym (lt  x≺y ¬x≡y ¬y≺x) = gt ¬y≺x (¬x≡y ∘ sym)  x≺y
tri-sym (eq ¬x≺y  x≡y ¬y≺x) = eq ¬y≺x (sym x≡y)    ¬x≺y
tri-sym (gt ¬x≺y ¬x≡y  y≺x) = lt  y≺x (¬x≡y ∘ sym) ¬x≺y
```
