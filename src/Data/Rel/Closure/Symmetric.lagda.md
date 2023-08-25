<!--
```agda
open import 1Lab.Prelude
open import Data.Sum

open import Data.Rel.Base
open import Data.Rel.Closure.Base
open import Data.Rel.Closure.Reflexive

import Data.Nat as Nat
import Data.Nat.Order as Nat
```
-->


```agda
module Data.Rel.Closure.Symmetric where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Symmetric Closure

The symmetric [closure] of a [relation] $R$ is the smallest symmetric
relation $R^{\leftrightarrow}$ that contains $R$.

[closure]: Data.Rel.Closure.html
[relation]: Data.Rel.Base.html

```agda
data Sym {A : Type ℓ} (R : A → A → Type ℓ') (x y : A) : Type (ℓ ⊔ ℓ') where
  symmetric : Sym R y x → Sym R x y
  [_] : R x y → Sym R x y
  trunc : is-prop (Sym R x y)
```

<!--
```agda
instance
  Sym-H-Level : ∀ {x y} {n} → H-Level (Sym R x y) (suc n)
  Sym-H-Level = prop-instance trunc

Sym-elim
  : (P : ∀ (x y : A) → Sym R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x y} → (r : Sym R y x) → P x y (symmetric r))
  → (∀ {x y} → (r+ : Sym R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Sym R x y) → P x y r+
Sym-elim {R = R} P prel psym pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Sym R x y) → P x y r+
  go (symmetric x) = psym x
  go [ x ] = prel x
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

Like the [reflexive closure], the recursion principle for the symmetric
closure witnesses it's universal property; it is the smallest symmetric
relation containing $R$.

[reflexive closure]: Data.Rel.Closure.Reflexive.html

```agda
Sym-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → R x y → S x y)
  → (∀ {x y} → S x y → S y x)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Sym R x y → S x y
Sym-rec {R = R} S prel psym pprop r+ = go r+ where
  go : ∀ {x y} → Sym R x y → S x y
  go (symmetric r) = psym (go r)
  go [ r ] = prel r
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

## As a closure operator

It is straightforward to show that the symmetric closure is a closure
operator.

```agda
sym-clo-mono : R ⊆r S → Sym R ⊆r Sym S
sym-clo-mono {S = S} p =
  Sym-rec (Sym S) (λ r → [ p r ]) symmetric trunc

sym-clo-closed : Sym (Sym R) ⊆r Sym R
sym-clo-closed {R = R} =
  Sym-rec (Sym R) id symmetric trunc

sym-closure : is-rel-closure Sym
sym-closure .is-rel-closure.monotone = sym-clo-mono
sym-closure .is-rel-closure.extensive = [_]
sym-closure .is-rel-closure.closed = sym-clo-closed
sym-closure .is-rel-closure.has-prop = trunc
```


## Properties

If two elements $x$ and $y$ are related in the symmetric closure, then
either $R x y$ or $R y x$ in the original relation.

```agda
sym-clo-rel
  : ∀ {x y} → Sym R x y → ∥ (R x y) ⊎ (R y x) ∥
sym-clo-rel {R = R} =
  Sym-rec (λ x y → ∥ (R x y) ⊎ (R y x) ∥)
    (λ r → inc (inl r))
    (∥-∥-map (⊎-rec inr inl))
    squash
```

If the original relation is reflexive, then so is the symmetric closure.

```agda
sym-clo-reflexive : is-reflexive R → is-reflexive (Sym R)
sym-clo-reflexive is-refl x = [ is-refl x ]
```

Note that this is *not* true for transitivity! To see why, consider an
irreflexive transitive relation on a type with at least related 2
elements $R x y$ . If the symmetric closure of this relation was
transitive, we'd be able to create a loop $R^{\leftrightarrow} x x$ in
the symmetric closure by composing the relations $R^{\leftrightarrow} x
y$ and $R^{\leftrightarrow} y x$.  However, if two elements are related
in the symmetric closure, then they must be related in the original
relation, which leads directly to a contradiction, as the original
relation is irreflexive.

For simplicity, we show this for the strict ordering on the natural
numbers.

```agda
private
  ¬sym-clo-transitive
    : ¬ (is-transitive (Sym Nat._<_))
  ¬sym-clo-transitive sym-clo-trans =
    ∥-∥-rec! (⊎-rec (Nat.<-irrefl refl) (Nat.<-irrefl refl))
      (sym-clo-rel (sym-clo-trans [ 0<1 ] (symmetric [ 0<1 ])))
    where
      0<1 : 0 Nat.< 1
      0<1 = Nat.s≤s Nat.0≤x
```

As a corollary, we can see that the transitive closure of the symmetric closure
is not the same as the symmetric closure of the transitive closure.

However, the reflexive closure of the symmetric closure is equal to the
symmetric closure of the reflexive closure.

```agda
sym-clo-refl-clo⊆refl-clo-sym-clo : Sym (Refl R) ⊆r Refl (Sym R)
sym-clo-refl-clo⊆refl-clo-sym-clo {R = R} =
  Sym-rec (Refl (Sym R))
    (Refl-rec (Refl (Sym R))
      (λ x~y → [ [ x~y ] ])
      (λ _ → reflexive)
      hlevel!)
    (Refl-rec (flipr (Refl (Sym R)))
      (λ y~x →  [ symmetric y~x ] )
      (λ _ → reflexive)
      hlevel!)
    hlevel!

refl-clo-sym-clo⊆sym-clo-refl-clo : Refl (Sym R) ⊆r Sym (Refl R)
refl-clo-sym-clo⊆sym-clo-refl-clo {R = R} =
  Refl-rec (Sym (Refl R))
    (Sym-rec (Sym (Refl R))
      (λ x~y → [ [ x~y ] ])
      symmetric
      hlevel!)
    (λ _ → [ reflexive ])
    hlevel!

refl-clo-sym-clo≡sym-clo-refl-clo : Refl (Sym R) ≡ Sym (Refl R)
refl-clo-sym-clo≡sym-clo-refl-clo =
  prop-rel-ext trunc trunc
    refl-clo-sym-clo⊆sym-clo-refl-clo
    sym-clo-refl-clo⊆refl-clo-sym-clo
```
