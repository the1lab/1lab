open import 1Lab.Prelude

open import Cat.Base

import Cat.Morphism

module Cat.Morphism.Extensionality {o ℓ} {C : Precategory o ℓ} where

open Cat.Morphism C

Extensional-≅
  : ∀ {ℓr} {a b}
  → {@(tactic extensionalᶠ Hom) sa : ∀ x y → Extensional (Hom x y) ℓr}
  → Extensional (a ≅ b) ℓr
Extensional-≅ {sa = sa} .Pathᵉ a b = Pathᵉ (sa _ _) (a .to) (b .to)
Extensional-≅ {sa = sa} .reflᵉ im = reflᵉ (sa _ _) (im .to)
Extensional-≅ {sa = sa} .idsᵉ = set-identity-system
  (λ x y → Pathᵉ-is-hlevel 1 (sa _ _) hlevel!)
  (λ p → ≅-path (sa _ _ .idsᵉ .to-path p))

instance
  extensionality-≅ : ∀ {a b} → Extensionality (a ≅ b)
  extensionality-≅ = record { lemma = quote Extensional-≅ }
