```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Type.Dec where
```

# Decidable types

A type is decidable if it's computable whether or not that type is
inhabited.

```agda
data Dec {ℓ} (A : Type ℓ) : Type ℓ where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

case : ∀ {ℓ ℓ'} {A : Type ℓ} (P : Dec A → Type ℓ')
     → ((y : A) → P (yes y))
     → ((y : (A → ⊥)) → P (no y))
     → (x : Dec A) → P x
case P f g (yes x) = f x
case P f g (no x) = g x
```

A type is _discrete_ if it has decidable equality.

```agda
Discrete : ∀ {ℓ} → Type ℓ → Type ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
```

<!--
```agda
private
  unyes : ∀ {ℓ} {A : Type ℓ} (p : Dec A) → (∀ {x} → p ≡ no x → ⊥) → A
  unyes (yes x₁) x = x₁
  unyes (no x₁) x = absurd (x refl)

  unno : ∀ {ℓ} {A : Type ℓ} (p : Dec A) → (∀ {x} → p ≡ yes x → ⊥) → A → ⊥
  unno (no x₁) x = x₁
  unno (yes x₁) x = absurd (x refl)

  yes≠no : ∀ {ℓ} {A : Type ℓ} {x : A} {p : A → ⊥} → yes x ≡ no p → ⊥
  yes≠no {x = x} {p = p} _ = p x

  lem1 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : yes x ≡ yes y) {n} i → p i ≡ no n → ⊥
  lem1 {x = x} p {n = n} i q = n x

  lem1′ : ∀ {ℓ} {A : Type ℓ} {x y : A → ⊥} (p : no x ≡ no y) {n} i → p i ≡ yes n → ⊥
  lem1′ {x = x} p {n = n} i q = x n

  yes-inj : ∀ {ℓ} {A : Type ℓ} {x y : A} → yes x ≡ yes y → x ≡ y
  yes-inj {x = x} p i = unyes (p i) (lem1 p i)

  no-inj : ∀ {ℓ} {A : Type ℓ} {x y : A → ⊥} → no x ≡ no y → x ≡ y
  no-inj {x = x} p i = unno (p i) (lem1′ p i)

  lem2 : ∀ {ℓ} {A : Type ℓ} (p : Dec A) (q : ∀ {x} → p ≡ no x → ⊥)
       → yes (unyes p q) ≡ p
  lem2 (yes x) q = refl
  lem2 (no x) q = absurd (q refl)

  lem2′
     : ∀ {ℓ} {A : Type ℓ} (p : Dec A) (q : ∀ {x} → p ≡ yes x → ⊥)
     → no (unno p q) ≡ p
  lem2′ (yes x) q = absurd (q refl)
  lem2′ (no x) q = refl

  yes-embed : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : yes x ≡ yes y)
            → ap yes (yes-inj p) ≡ p
  yes-embed p i j = lem2 (p j) (lem1 p j) i

  no-embed : ∀ {ℓ} {A : Type ℓ} {x y : A → ⊥} (p : no x ≡ no y)
           → ap no (no-inj p) ≡ p
  no-embed p i j = lem2′ (p j) (lem1′ p j) i

instance
  H-Level-Dec : ∀ {n} {ℓ} {A : Type ℓ} ⦃ hl : H-Level A (suc n) ⦄
              → H-Level (Dec A) (suc n)
  H-Level-Dec {n = zero} = prop-instance λ where
    (yes x) (yes x₁) i → yes (hlevel 1 x x₁ i)
    (yes x) (no x₁) → absurd (x₁ x)
    (no x) (yes x₁) → absurd (x x₁)
    (no x) (no x₁) i → no (hlevel 1 x x₁ i)
  H-Level-Dec {n = suc n} = hlevel-instance λ where
    (yes x) (yes x₁)  → retract→is-hlevel (suc n) (ap yes) yes-inj yes-embed (hlevel (suc n))
    (yes x) (no x₁)   → absurd (x₁ x)
    (no x) (yes x₁)   → absurd (x x₁)
    (no ¬x1) (no ¬x2) → retract→is-hlevel (suc n) (ap no) no-inj no-embed (hlevel (suc n))
```
-->
