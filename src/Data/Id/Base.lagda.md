```agda
{-# OPTIONS -WUnsupportedIndexedMatch #-}
open import 1Lab.Path.IdentitySystem
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Type
open import 1Lab.Path

open import Data.Dec.Base

module Data.Id.Base where
```

# Inductive identity

In cubical type theory, we generally use the [path] types to represent
identifications. But in cubical type theory with indexed inductive
types, we have a different --- but equivalent --- choice: the inductive
_identity type_.

[path]: 1Lab.Path.html

```agda
data _≡ᵢ_ {ℓ} {A : Type ℓ} (x : A) : A → Type ℓ where
  reflᵢ : x ≡ᵢ x
```

To show that $\rm{Id}_A(x,y)$ is equivalent to $x \equiv y$ for every
type $A$, we'll show that `_≡ᵢ_`{.Agda} and `reflᵢ`{.Agda} form an
[identity system] regardless of the underlying type. Since `Id`{.Agda}
is an inductive type, we can do so by pattern matching, which results in
a very slick definition:

[identity system]: 1Lab.Path.IdentitySystem.html

```agda
Id-identity-system
  : ∀ {ℓ} {A : Type ℓ}
  → is-identity-system (_≡ᵢ_ {A = A}) (λ _ → reflᵢ)
Id-identity-system .to-path      reflᵢ = refl
Id-identity-system .to-path-over reflᵢ = refl
```

Paths are, in many ways, more convenient than the inductive identity
type: as a (silly) example, for paths, we have $(p^{-1})^{-1}$
definitionally. But the inductive identity type has _one_ property which
sets it apart from paths: **regularity.** Transport along the
reflexivity path is definitionally the identity:

```agda
substᵢ : ∀ {ℓ ℓ′} {A : Type ℓ} (P : A → Type ℓ′) {x y : A}
       → x ≡ᵢ y → P x → P y
substᵢ P reflᵢ x = x

_ : ∀ {ℓ} {A : Type ℓ} {x : A} → substᵢ (λ x → x) reflᵢ x ≡ x
_ = refl
```

<!--
```agda
_ = _≡_
Id≃path : ∀ {ℓ} {A : Type ℓ} {x y : A} → (x ≡ᵢ y) ≃ (x ≡ y)
Id≃path {ℓ} {A} {x} {y} =
  identity-system-gives-path (Id-identity-system {ℓ = ℓ} {A = A}) {a = x} {b = y}

module Id≃path {ℓ} {A : Type ℓ} {x y : A} = Equiv (Id≃path {ℓ} {A} {x} {y})
```
-->

In the 1Lab, we prefer `_≡_`{.Agda} over `_≡ᵢ_`{.Agda} --- which is why
there is no comprehensive toolkit for working with the latter. But it
can still be used when we want to _avoid_ transport along reflexivity,
for example, when working with decidable equality of concrete (indexed)
types like [`Fin`].

[`Fin`]: Data.Fin.Base.html

```agda
Discreteᵢ : ∀ {ℓ} → Type ℓ → Type ℓ
Discreteᵢ A = (x y : A) → Dec (x ≡ᵢ y)

Discreteᵢ→discrete : ∀ {ℓ} {A : Type ℓ} → Discreteᵢ A → Discrete A
Discreteᵢ→discrete d x y with d x y
... | yes reflᵢ = yes refl
... | no ¬x=y   = no λ p → ¬x=y (Id≃path.from p)

is-set→is-setᵢ : ∀ {ℓ} {A : Type ℓ} → is-set A → (x y : A) (p q : x ≡ᵢ y) → p ≡ q
is-set→is-setᵢ A-set x y p q = Id≃path.injective (A-set _ _ _ _)

≡ᵢ-is-hlevel' : ∀ {ℓ} {A : Type ℓ} {n} → is-hlevel A (suc n) → (x y : A) → is-hlevel (x ≡ᵢ y) n
≡ᵢ-is-hlevel' {n = n} ahl x y = subst (λ e → is-hlevel e n) (sym (ua Id≃path)) (Path-is-hlevel' n ahl x y)
```
