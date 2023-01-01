```agda
open import Cat.Prelude
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal

open import Data.List
open import Data.Sum

open import Theories.Signature

module Theories.Simple.Model
  {o ℓ} (𝒞 : Precategory o ℓ)
  (has-prods : ∀ A B → Product 𝒞 A B)
  (has-terminal : Terminal 𝒞)
  where

open Precategory 𝒞
open Cartesian 𝒞 has-prods
open Terminal has-terminal
open Sign
```

# Models of Signatures

```agda
tensor-list : ∀ {ℓ} {A : Type ℓ} → (A → Ob) → List A → Ob
tensor-list f = foldr (λ x → f x ⊗_) top
```

```agda
record Model {s} (Sg : Sign s) : Type (o ⊔ ℓ ⊔ s) where
  no-eta-equality
  field
    ⟦_⟧ₒ : ∣ Sort Sg ∣ → Ob

  ⟦_⟧ᵢ : List ∣ Sort Sg ∣ → Ob
  ⟦ Γ ⟧ᵢ = tensor-list ⟦_⟧ₒ Γ

  field
    mor : ∀ Γ X → ∣ Op Sg Γ X ∣ → Hom ⟦ Γ ⟧ᵢ ⟦ X ⟧ₒ

{-# DISPLAY Model.⟦_⟧ᵢ Γ = tensor-list Model.⟦_⟧ₒ Γ #-}
```

