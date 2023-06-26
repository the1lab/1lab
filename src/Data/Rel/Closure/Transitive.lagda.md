<!--
```agda
open import 1Lab.Prelude
open import Data.Sum

open import Data.Rel.Base
open import Data.Rel.Closure.Base
```
-->

```agda
module Data.Rel.Closure.Transitive where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Transitive Closure

The transitive [closure] of a [relation] $R$ is the smallest transitive
relation $R^{+}$ that contains $R$.

[relation]: Data.Rel.Base.html
[closure]: Data.Rel.Closure.html

```agda
data Trans {A : Type ℓ} (_~_ : Rel A A ℓ') (x z : A) : Type (ℓ ⊔ ℓ') where
  [_] : x ~ z → Trans _~_ x z
  transitive : ∀ {y} → Trans _~_ x y → Trans _~_ y z → Trans _~_ x z
  trunc : is-prop (Trans _~_ x z)
```

<!--
```agda
instance
  Trans-H-Level : ∀ {x y} {n} → H-Level (Trans R x y) (suc n)
  Trans-H-Level = prop-instance trunc

Trans-elim
  : (P : ∀ (x y : A) → Trans R x y → Type ℓ)
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x y z} → (r+ : Trans R x y) → (s+ : Trans R y z)
     → P x y r+ → P y z s+
     → P x z (transitive r+ s+))
  → (∀ {x y} → (r+ : Trans R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Trans R x y) → P x y r+
Trans-elim {R = R} P prel ptrans pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Trans R x y) → P x y r+
  go [ r ] = prel r
  go (transitive r+ s+) = ptrans r+ s+ (go r+) (go s+)
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

The recursion principle for the transitive closure witnesses it's
universal property; it is the smallest transitive relation containing $R$.

```agda
Trans-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → (r : R x y) → S x y)
  → (∀ {x y z} → S x y → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Trans R x y → S x y
Trans-rec {R = R} S prel ptrans pprop r+ = go r+ where
  go : ∀ {x y} → Trans R x y → S x y
  go [ r ] = prel r
  go (transitive r+ s+) = ptrans (go r+) (go s+)
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

## As a closure operator

```agda
trans-clo-mono : R ⊆r S → Trans R ⊆r Trans S
trans-clo-mono {S = S} p =
  Trans-rec (Trans S) (λ r → [ p r ]) transitive trunc

trans-clo-closed : Trans (Trans R) ⊆r Trans R
trans-clo-closed {R = R} =
  Trans-rec (Trans R) id transitive trunc

trans-closure : is-rel-closure Trans
trans-closure .is-rel-closure.monotone = trans-clo-mono
trans-closure .is-rel-closure.extensive = [_]
trans-closure .is-rel-closure.closed = trans-clo-closed
trans-closure .is-rel-closure.has-prop = trunc
```

## Properties

If the original relation is reflexive or symmetric, then so is the
transitive closure.

```agda
trans-clo-reflexive : is-reflexive R → is-reflexive (Trans R)
trans-clo-reflexive is-refl x = [ is-refl x ]

trans-clo-symmetric : is-symmetric R → is-symmetric (Trans R)
trans-clo-symmetric {R = R} is-sym r+ =
  Trans-rec (λ x y → Trans R y x)
    (λ r → [ is-sym r ])
    (λ r+ s+ → transitive s+ r+)
    trunc
    r+
```
