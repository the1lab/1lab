---
description: |
  Reasoning with ordinals.
---
≺!--
```agda
open import Cat.Prelude

open import Data.Wellfounded.Base

open import Order.Ordinal
```
-->
```agda
module Order.Ordinal.Reasoning {o ℓ} (X : Ordinal o ℓ) where
```

# Reasoning with ordinals

```agda
open Ordinal X public

data ≺-Reasoning (x y : Ob) : Type (o ⊔ ℓ) where
  strong : x ≺ y → ≺-Reasoning x y
  weak : x ≡ y → ≺-Reasoning x y

private
  is-strong : ∀ {x y} → ≺-Reasoning x y → Type
  is-strong (strong _) = ⊤
  is-strong (weak _) = ⊥

begin-≺_ : ∀ {x y} → (x≺y : ≺-Reasoning x y) → { is-strong x≺y } → x ≺ y
begin-≺ (strong x≺y) = x≺y

step-≺ : ∀ x {y z} → ≺-Reasoning y z → x ≺ y → ≺-Reasoning x z
step-≺ x (strong y≺z) x≺y = strong (≺-trans x≺y y≺z)
step-≺ x (weak y=z) x≺y = strong (≺-whiskerr x≺y y=z)

step-≡ : ∀ x {y z} → ≺-Reasoning y z → x ≡ y → ≺-Reasoning x z
step-≡ x (strong y≺z) x=y = strong (≺-whiskerl x=y y≺z)
step-≡ x (weak y=z) x=y = weak (x=y ∙ y=z)

step-≡˘ : ∀ x {y z} → ≺-Reasoning y z → y ≡ x → ≺-Reasoning x z
step-≡˘ x y p = step-≡ x y (sym p)

_≺∎ : ∀ x → ≺-Reasoning x x
_≺∎ x = weak refl

infix  1 begin-≺_
infixr 2 step-≺
infixr 2 step-≡
infixr 2 step-≡˘

syntax step-≺ x q p = x ≺⟨ p ⟩ q
syntax step-≡ x q p = x =⟨ p ⟩ q
syntax step-≡˘ x q p = x =˘⟨ p ⟩ q
infix  3 _≺∎
```

```agda
≺-elim
  : ∀ {κ} (P : Ob → Type κ)
  → (∀ x₀ → (∀ y → y ≺ x₀ → P y) → P x₀)
  → ∀ x₀ → P x₀
≺-elim = Wf-induction _≺_ ≺-wf

≺-elim₂
  : ∀ {κ} (P : Ob → Ob → Type κ)
    → (∀ x y
     → (∀ a → a ≺ x → P a y)
     → (∀ b → b ≺ y → P x b)
     → (∀ a b → a ≺ x → b ≺ y → P a b)
     → P x y)
  → ∀ x y → P x y
≺-elim₂ = Wf-induction₂ _≺_ ≺-wf

≺-bounded-elim
  : ∀ {κ} {x : Ob}
  → (P : (x₀ : Ob) → x₀ ≺ x → Type κ)
  → (∀ x₀ → (x₀≺x : x₀ ≺ x) → (∀ y → (y≺x₀ : y ≺ x₀) → P y (≺-trans y≺x₀ x₀≺x)) → P x₀ x₀≺x)
  → ∀ x₀ → (x₀≺x : x₀ ≺ x) → P x₀ x₀≺x
≺-bounded-elim {x = x} P work =
  ≺-elim (λ x₀ → (x₀≺x : x₀ ≺ x) → P x₀ x₀≺x) λ x₀ rec x₀≺x →
    work x₀ x₀≺x (λ y y≺x₀ → rec y y≺x₀ (≺-trans y≺x₀ x₀≺x))
```

```agda
≺-irrefl : ∀ {x} → x ≺ x → ⊥
≺-irrefl {x} x≺x =
  ≺-elim (λ x₀ → x ≺ x₀ → ⊥)
    (λ x₀ rec x≺x₀ → rec x x≺x₀ x≺x)
    x x≺x

≺-asym : ∀ {x y} → x ≺ y → y ≺ x → ⊥
≺-asym x≺y y≺x = ≺-irrefl (≺-trans x≺y y≺x)
```

```agda
_≼_ : Ob → Ob → Type (o ⊔ ℓ)
x ≼ y = ∀ a → a ≺ x → a ≺ y

≼-refl : ∀ {x} → x ≼ x
≼-refl a a≺x = a≺x

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans x≼y y≼z a a≺x = y≼z a (x≼y a a≺x)

≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
≼-antisym = ≺-ext

≺-weaken : ∀ {x y} → x ≺ y → x ≼ y
≺-weaken x≺y a a≺x = ≺-trans a≺x x≺y

≼-transr : ∀ {x y z} → x ≺ y → y ≼ z → x ≺ z
≼-transr x≺y y≼z = y≼z _ x≺y

path→≼ : ∀ {x y} → x ≡ y → x ≼ y
path→≼ p a a≺x = subst (a ≺_) p a≺x
```
