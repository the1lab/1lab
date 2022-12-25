```agda
open import 1Lab.Path
open import 1Lab.Type

module Data.Dec.Base where
```

# Decidable types

The type `Dec`{.Agda}, of **decisions** for a type `A`, is a renaming of
the coproduct `A + ¬ A`. A value of `Dec A` witnesses not that `A`
is decidable, but that it _has been decided_; A witness of decidability,
then, is a proof assigning decisions to values of a certain type.

```agda
data Dec {ℓ} (A : Type ℓ) : Type ℓ where
  yes : (a  :   A) → Dec A
  no  : (¬a : ¬ A) → Dec A

Dec-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} (P : Dec A → Type ℓ')
  → (∀ y → P (yes y))
  → (∀ y → P (no y))
  → ∀ x → P x
Dec-elim P f g (yes x) = f x
Dec-elim P f g (no x)  = g x
```

<!--
```agda
recover : ∀ {ℓ} {A : Type ℓ} → Dec A → .A → A
recover (yes x) _ = x
recover {A = A} (no ¬x) x = go (¬x x) where
  go : .⊥ → A
  go ()
```
-->

A type is _discrete_ if it has decidable equality.

```agda
Discrete : ∀ {ℓ} → Type ℓ → Type ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
```
