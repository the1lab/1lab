open import 1Lab.Prelude

open import Cat.Base

import Cat.Morphism

module Cat.Morphism.Extensionality {o ℓ} {C : Precategory o ℓ} where

open Cat.Morphism C

Extensional-≅
  : ∀ {ℓr} {a b}
  → ⦃ sa : Extensional (Hom a b) ℓr ⦄
  → Extensional (a ≅ b) ℓr
Extensional-≅ ⦃ sa ⦄ .Pathᵉ a b = Pathᵉ sa (a .to) (b .to)
Extensional-≅ ⦃ sa ⦄ .reflᵉ im = reflᵉ sa (im .to)
Extensional-≅ ⦃ sa ⦄ .idsᵉ = set-identity-system
  (λ x y → Pathᵉ-is-hlevel 1 sa hlevel!)
  (λ p → ≅-path (sa .idsᵉ .to-path p))

instance
  extensionality-≅ : ∀ {a b} → Extensionality (a ≅ b)
  extensionality-≅ = record { lemma = quote Extensional-≅ }
