```agda
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

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
```
