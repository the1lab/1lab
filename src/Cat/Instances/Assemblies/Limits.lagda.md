<!--
```agda
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base

open import Realisability.PCA

import Cat.Instances.Assemblies

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Base
```
-->

```agda
module Cat.Instances.Assemblies.Limits
  {ℓA} {A : Type ℓA} ⦃ _ : H-Level A 2 ⦄ {_%_ : ↯ A → ↯ A → ↯ A} (p : is-pca _%_)
  where
```

<!--
```agda
open Cat.Instances.Assemblies p
open Realisability.Data.Pair p
open Realisability.PCA.Sugar p
open Realisability.Base p

open is-product
open Product

open [_]_⊢_

private variable
  ℓ ℓ' : Level
  X Y Z : Assembly ℓ
```
-->

# Finite limits of assemblies

```agda
_×Asm_ : Assembly ℓ → Assembly ℓ' → Assembly (ℓ ⊔ ℓ')
(X ×Asm Y) .Ob         = ⌞ X ⌟ × ⌞ Y ⌟
(X ×Asm Y) .has-is-set = hlevel 2

(X ×Asm Y) .realisers (x , y) = record
  { mem     = λ p → elΩ do
    Σ[ a ∈ ↯ A ] Σ[ b ∈ ↯ A ]
      p ≡ `pair ⋆ a ⋆ b × [ X ] a ⊩ x × [ Y ] b ⊩ y
  ; defined = rec! λ a b p rx ry →
    subst ⌞_⌟ (sym p) (`pair↓₂ (X .defined rx) (Y .defined ry))
  }

(X ×Asm Y) .realised (x , y) = do
  (px , rx) ← X .realised x
  (py , ry) ← Y .realised y
  pure (`pair ⋆ px ⋆ py , inc (px , py , refl , rx , ry))
```

```agda
Assemblies-products : has-products (Assemblies ℓ)
Assemblies-products X Y .apex = X ×Asm Y
Assemblies-products X Y .π₁ = record
  { map     = fst
  ; tracked = inc record
    { realiser = `fst
    ; tracks   = elim! λ a p q α rx ry → subst⊩ X rx $
      ap (`fst ⋆_) α ∙ `fst-β (X .defined rx) (Y .defined ry)
    }
  }
Assemblies-products X Y .π₂ = record
  { map     = snd
  ; tracked = inc record
    { realiser = `snd
    ; tracks   = elim! λ a p q α rx ry → subst⊩ Y ry $
      ap (`snd ⋆_) α ∙ `snd-β (X .defined rx) (Y .defined ry)
    }
  }

Assemblies-products X Y .has-is-product .⟨_,_⟩ {Q = Q} f g = record
  { map     = λ x → f · x , g · x
  ; tracked = case f .tracked of λ rf → case g .tracked of λ rg → inc record
    { realiser = val ⟨ x ⟩ `pair `· (rf `· x) `· (rg `· x)
    ; tracks   = λ a qx → inc
      ( rf ⋆ a , rg ⋆ a , abs-β _ _ (a , Q .defined qx)
      , rf .tracks a qx , rg .tracks a qx )
    }
  }

Assemblies-products X Y .has-is-product .π₁∘⟨⟩ = ext λ _ → refl
Assemblies-products X Y .has-is-product .π₂∘⟨⟩ = ext λ _ → refl
Assemblies-products X Y .has-is-product .unique p q = ext λ a →
  ap map p · a ,ₚ ap map q · a
```
