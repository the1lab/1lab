```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Instances.Sets
open import Cat.Instances.Sets.Complete
open import Cat.Prelude

open import Data.List

open import Theories.Signature
import Theories.Simple.Syntax as Syntax
import Theories.Simple.Model as Models

module Theories.Simple.Classifying where

module SetModels κ = Models (Sets κ) Sets-products Sets-terminal
open SetModels
open Model
```

# The classifying category of a signature

```agda
Cl : ∀ {ℓ} → Sign ℓ → Precategory ℓ ℓ
Cl {ℓ = ℓ} Sg = cat where
  open Sign Sg
  open Syntax Sg
  open Precategory

  cat : Precategory ℓ ℓ
  cat .Ob = List ∣ Sort ∣
  cat .Hom Γ Δ = Subst Γ Δ
  cat .Hom-set Γ Δ = hlevel!
  cat .id = idₛ
  cat ._∘_ = _∘ₛ_
  cat .idr = ∘ₛ-idr
  cat .idl = ∘ₛ-idl
  cat .assoc = ∘ₛ-assoc
```

## Products

```agda
module _ {ℓ} (Sg : Sign ℓ) where
  open Sign Sg
  open Syntax Sg

  Cl-products : ∀ (Γ Δ : List ∣ Sort ∣) → Product (Cl Sg) Γ Δ
  Cl-products Γ Δ .Product.apex = Γ ++ Δ
  Cl-products Γ Δ .Product.π₁ = fstₛ
  Cl-products Γ Δ .Product.π₂ = sndₛ
  Cl-products Γ Δ .Product.has-is-product .is-product.⟨_,_⟩ = ⟨_,_⟩ₛ
  Cl-products Γ Δ .Product.has-is-product .is-product.π₁∘factor =
    subext (fstₛ-⟨⟩ₛ _ _)
  Cl-products Γ Δ .Product.has-is-product .is-product.π₂∘factor =
    subext (sndₛ-⟨⟩ₛ _ _)
  Cl-products Γ Δ .Product.has-is-product .is-product.unique σ p q =
    subext (⟨⟩ₛ-unique _ _ σ p q)

  Cl-terminal : Terminal (Cl Sg)
  Cl-terminal .Terminal.top = []
  Cl-terminal .Terminal.has⊤ Γ .centre = sub λ ()
  Cl-terminal .Terminal.has⊤ Γ .paths σ = subext λ ()
```

