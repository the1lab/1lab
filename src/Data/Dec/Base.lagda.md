<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module Data.Dec.Base where
```

# Decidable types {defines="decidable type-of-decisions discrete"}

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

Dec-rec
  : ∀ {ℓ ℓ'} {A : Type ℓ} {X : Type ℓ'}
  → (A → X)
  → (¬ A → X)
  → Dec A → X
Dec-rec = Dec-elim _
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

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B : Type ℓ
```
-->

If we can construct a pair of maps $A \to B$ and $B \to A$,
then we can deduce decidability of $B$ from decidability of $A$.

```agda
Dec-map
  : (A → B) → (B → A)
  → Dec A → Dec B
Dec-map to from (yes a) = yes (to a)
Dec-map to from (no ¬a) = no (¬a ∘ from)
```

This lets us show the following useful lemma: if $A$ injects into a
discrete type, then $A$ is also discrete.

```agda
Discrete-inj
  : (f : A → B)
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Discrete B → Discrete A
Discrete-inj f inj eq? x y =
  Dec-map inj (ap f) (eq? (f x) (f y))
```

<!--
```agda
infix 0 ifᵈ_then_else_

ifᵈ_then_else_ : Dec A → B → B → B
ifᵈ yes a then y else n = y
ifᵈ no ¬a then y else n = n
```
-->
