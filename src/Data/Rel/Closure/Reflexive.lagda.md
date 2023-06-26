<!--
```agda
open import 1Lab.Prelude

open import Data.Rel.Base
open import Data.Rel.Closure.Base
```
-->

```agda
module Data.Rel.Closure.Reflexive where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Reflexive Closure

The reflexive [closure] of a [relation] $R$ is the smallest reflexive
relation $R^{=}$ that contains $R$.

[relation]: Data.Rel.Base.html
[closure]: Data.Rel.Closure.html

```agda
data Refl {A : Type ℓ} (R : Rel A A ℓ') (x : A) : A → Type (ℓ ⊔ ℓ') where
  reflexive : Refl R x x
  [_] : ∀ {y} → R x y → Refl R x y
  trunc : ∀ {y} → is-prop (Refl R x y)
```

<!--
```agda
instance
  Refl-H-Level : ∀ {x y} {n} → H-Level (Refl R x y) (suc n)
  Refl-H-Level = prop-instance trunc

Refl-elim
  : (P : ∀ (x y : A) → Refl R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ x → P x x reflexive)
  → (∀ {x y} → (r+ : Refl R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Refl R x y) → P x y r+
Refl-elim {R = R} P prel prefl pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Refl R x y) → P x y r+
  go reflexive = prefl _
  go [ x ] = prel x
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

The recursion principle for the reflexive closure of a relation witnesses
the aforementioned universal property: it is the smallest reflexive
relation containing $R$.

```agda
Refl-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → R x y → S x y)
  → (∀ x → S x x)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl R x y → S x y
Refl-rec {R = R} S prel prefl pprop r+ = go r+ where
  go : ∀ {x y} → Refl R x y → S x y
  go reflexive = prefl _
  go [ r ] = prel r
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

<!--
```agda
Refl-rec₂
  : (S : A → A → A → Type ℓ)
  → (∀ {x y z} → R x y → R' y z → S x y z)
  → (∀ {x z} → R' x z → S x x z)
  → (∀ {x y} → R x y → S x y y)
  → (∀ x → S x x x)
  → (∀ {x y z} → is-prop (S x y z))
  → ∀ {x y z} → Refl R x y → Refl R' y z → S x y z
Refl-rec₂ {R = R} {R' = R'} S prel prefll preflr prefl2 pprop r+ r+' = go r+ r+' where
  go : ∀ {x y z} → Refl R x y → Refl R' y z → S x y z
  go reflexive reflexive = prefl2 _
  go reflexive [ r' ] = prefll r'
  go reflexive (trunc r+ r+' i) =
    pprop (go reflexive r+) (go reflexive r+') i
  go [ r ] reflexive = preflr r
  go [ r ] [ r' ] = prel r r'
  go [ r ] (trunc r+ r+' i) =
    pprop (go [ r ] r+) (go [ r ] r+') i
  go (trunc r+ r+' i) r+'' =
    pprop (go r+ r+'') (go r+' r+'') i
```
-->


## As a closure operator

As the name suggests, the reflexive closure of a relation forms a closure
operator.

```agda
refl-clo-mono : R ⊆r S → Refl R ⊆r Refl S
refl-clo-mono {S = S} p =
  Refl-rec (Refl S) (λ r → [ p r ]) (λ _ → reflexive) trunc 

refl-clo-closed : Refl (Refl R) ⊆r Refl R
refl-clo-closed {R = R} = Refl-rec (Refl R) id (λ _ → reflexive) trunc

refl-closure : is-rel-closure Refl
refl-closure .is-rel-closure.monotone = refl-clo-mono
refl-closure .is-rel-closure.extensive = [_]
refl-closure .is-rel-closure.closed = refl-clo-closed
refl-closure .is-rel-closure.has-prop = trunc
```

## Properties

If the original relation is symmetric or transitive, then so is the
reflexive closure.

```agda
refl-clo-symmetric
  : is-symmetric R
  → is-symmetric (Refl R)
refl-clo-symmetric {R = R} is-sym =
  Refl-rec (λ x y → Refl R y x)
    (λ r → [ is-sym r ])
    (λ _ → reflexive)
    trunc

refl-clo-transitive : is-transitive R → is-transitive (Refl R)
refl-clo-transitive {R = R} is-trans =
    Refl-rec₂ (λ x _ z → Refl R x z)
      (λ x~*y y~*z → [ is-trans x~*y y~*z ])
      [_]
      [_]
      (λ _ → reflexive)
      trunc
```
