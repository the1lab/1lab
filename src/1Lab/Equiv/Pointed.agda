open import 1Lab.Type.Pointed
open import 1Lab.Univalence
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Equiv.Pointed where

_≃∙_ : ∀ {ℓ ℓ'} → Type∙ ℓ → Type∙ ℓ' → Type _
(A , a₀) ≃∙ (B , b₀) = Σ[ e ∈ A ≃ B ] (e .fst a₀ ≡ b₀)

ua∙ : ∀ {ℓ} {A B : Type∙ ℓ} → A ≃∙ B → A ≡ B
ua∙ (e , p) i .fst = ua e i
ua∙ (e , p) i .snd = attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ }) (inS (p i))

module Equiv∙ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} (e : A ≃∙ B) where
  open Equiv (e .fst) hiding (inverse) public

  inverse : B ≃∙ A
  inverse .fst = Equiv.inverse (e .fst)
  inverse .snd = Equiv.injective (e .fst) (Equiv.ε (e .fst) _ ∙ sym (e .snd))

id≃∙ : ∀ {ℓ} {A : Type∙ ℓ} → A ≃∙ A
id≃∙ = id≃ , refl

≃∙⟨⟩-syntax : ∀ {ℓ ℓ₁ ℓ₂} (A : Type∙ ℓ) {B : Type∙ ℓ₁} {C : Type∙ ℓ₂}
            → B ≃∙ C → A ≃∙ B → A ≃∙ C
≃∙⟨⟩-syntax A (g , pt) (f , pt') = f ∙e g , ap (g .fst) pt' ∙ pt

_≃∙˘⟨_⟩_ : ∀ {ℓ ℓ₁ ℓ₂} (A : Type∙ ℓ) {B : Type∙ ℓ₁} {C : Type∙ ℓ₂}
        → B ≃∙ A → B ≃∙ C → A ≃∙ C
A ≃∙˘⟨ f ⟩ g = ≃∙⟨⟩-syntax _ g (Equiv∙.inverse f)

_≃∙⟨⟩_ : ∀ {ℓ ℓ₁} (A : Type∙ ℓ) {B : Type∙ ℓ₁} → A ≃∙ B → A ≃∙ B
x ≃∙⟨⟩ x≡y = x≡y

_≃∙∎ : ∀ {ℓ} (A : Type∙ ℓ) → A ≃∙ A
x ≃∙∎ = id≃∙

infixr 2 ≃∙⟨⟩-syntax _≃∙⟨⟩_ _≃∙˘⟨_⟩_
infix  3 _≃∙∎
infix 21 _≃∙_

syntax ≃∙⟨⟩-syntax x q p = x ≃∙⟨ p ⟩ q
