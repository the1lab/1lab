<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties

open import Homotopy.Connectedness
```
-->

```agda
module Homotopy.Wedge where
```

# Wedge connectivity

```agda
module
  Wedge
    {ℓ ℓ' ℓ''} {A∙@(A , a₀) : Type∙ ℓ} {B∙@(B , b₀) : Type∙ ℓ'} {P : A → B → Type ℓ''}
    (n m : Nat)
    (a-conn : is-n-connected A (2 + n))
    (b-conn : is-n-connected B (2 + m))
    (p-hl : ∀ x y → is-hlevel (P x y) (2 + n + m))
    (f : ∀ a → P a b₀) (g : ∀ b → P a₀ b) (coh : f a₀ ≡ g b₀)
  where

  private
    Q : A → Type (ℓ' ⊔ ℓ'')
    Q a = Σ ((b : B) → P a b) (λ k → k b₀ ≡ f a)

    rem₂' : (x : A) → is-hlevel (fibre (_∘ (λ _ → b₀)) (λ _ → f x)) (1 + n)
    rem₂' a = relative-n-type-const-plus {A = ⊤} (P a) (λ _ → b₀) (suc m) (suc n)
      (point-is-n-connected b₀ m b-conn)
      (λ b → subst (is-hlevel (P a b)) (sym (ap suc (+-sucr n m))) (p-hl a b))
      (λ _ → f a)

    opaque
      worker : Σ ((b : A) → Q b) (λ h → Path (⊤ → Q a₀) (λ _ → h a₀) (λ _ → g , sym coh))
      worker = connected-elimination-principle (suc n) Q hl (g , sym coh) a-conn where
        hl : (x : A) → is-hlevel (Q x) (suc n)
        hl x = retract→is-hlevel (suc n)
          (λ (p , q) → p , happly q tt)
          (λ (p , q) → p , funext λ _ → q)
          (λ _ → refl) (rem₂' x)

  opaque
    elim : ∀ x y → P x y
    elim x y = worker .fst x .fst y

    β₁ : ∀ a → elim a b₀ ≡ f a
    β₁ a = worker .fst a .snd

    β₂ : ∀ b → elim a₀ b ≡ g b
    β₂ b = ap fst (worker .snd $ₚ tt) $ₚ b

    β-path : β₂ b₀ ∙ sym coh ≡ β₁ a₀
    β-path = square→commutes (ap snd (worker .snd $ₚ tt)) ∙ ∙-idr _
```
