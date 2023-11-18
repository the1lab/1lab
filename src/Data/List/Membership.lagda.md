<!--
```agda
open import 1Lab.Prelude
open import Data.List.Base
open import Data.Sum
open import Data.Dec
```
-->

```agda
module Data.List.Membership where

data Some {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ ⊔ ℓ') where
  here : ∀ {x xs} → P x → Some P (x ∷ xs)
  there : ∀ {x xs} → Some P xs → Some P (x ∷ xs)

_∈ₗ_ : ∀ {ℓ} {A : Type ℓ} → A → List A → Type ℓ
x ∈ₗ [] = Lift _ ⊥
x ∈ₗ (y ∷ xs) = x ≡ y ⊎ (x ∈ₗ xs)
```

<!--
```agda
private
  variable
    ℓ : Level
    A : Type ℓ
```
-->

```agda
elem? : Discrete A → (x : A) → (xs : List A) → Dec (x ∈ₗ xs)
elem? eq? x [] = no Lift.lower
elem? eq? x (y ∷ xs) =
  Dec-rec (yes ∘ inl)
    (λ x≠y →
      Dec-rec (yes ∘ inr)
        (λ x∉xs → no [ x≠y , x∉xs ])
        (elem? eq? x xs))
    (eq? x y)
```
