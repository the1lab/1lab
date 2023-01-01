```agda
open import Cat.Prelude
open import Cat.Diagram.Product
open import Cat.Diagram.Product.Solver
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base
open import Cat.Displayed.Total

import Cat.Reasoning

open import Data.List
open import Data.Sum

open import Theories.Signature

module Theories.Simple.Model
  {o ℓ} (𝒞 : Precategory o ℓ)
  (has-prods : ∀ A B → Product 𝒞 A B)
  (has-terminal : Terminal 𝒞)
  where

open Cat.Reasoning 𝒞
open Cartesian 𝒞 has-prods
open Terminal has-terminal
open Sign

open Total-hom
```

# Models of Signatures

```agda
tensor-list : ∀ {ℓ} {A : Type ℓ} → (A → Ob) → List A → Ob
tensor-list f = foldr (λ x → f x ⊗_) top

tensor-hom : ∀ {ℓ} {A : Type ℓ}
           → {P Q : A → Ob}
           → (∀ x → Hom (P x) (Q x))
           → (xs : List A)
           → Hom (tensor-list P xs) (tensor-list Q xs)
tensor-hom α [] = !
tensor-hom α (x ∷ xs) = ⟨ α x ∘ π₁ , tensor-hom α xs ∘ π₂ ⟩

tensor-hom-id : ∀ {ℓ} {A : Type ℓ}
              → {P : A → Ob}
              → (xs : List A)
              → tensor-hom {P = P} (λ _ → id) xs ≡ id
tensor-hom-id [] =
  !-unique id 
tensor-hom-id (x ∷ xs) =
  sym $ ⟨⟩-unique id id-comm (idr _ ∙ introl (tensor-hom-id xs))

tensor-hom-∘ : ∀ {ℓ} {A : Type ℓ}
              → {P Q R : A → Ob}
              → (α : ∀ x → Hom (Q x) (R x))
              → (β : ∀ x → Hom (P x) (Q x))
              → (xs : List A)
              → tensor-hom (λ x → α x ∘ β x) xs ≡ tensor-hom α xs ∘ tensor-hom β xs
tensor-hom-∘ α β [] =
  !-unique (! ∘ !)
tensor-hom-∘ α β (x ∷ xs) =
  ⟨ (α x ∘ β x) ∘ π₁ , ⌜ tensor-hom (λ x → α x ∘ β x) xs ⌝ ∘ π₂ ⟩                ≡⟨ ap! (tensor-hom-∘ α β xs) ⟩
  ⟨ (α x ∘ β x) ∘ π₁ , (tensor-hom α xs ∘ tensor-hom β xs) ∘ π₂ ⟩                ≡⟨ products! 𝒞 has-prods ⟩
  ⟨ α x ∘ π₁ , tensor-hom α xs ∘ π₂ ⟩ ∘  ⟨ β x ∘ π₁ , tensor-hom β xs ∘ π₂ ⟩     ∎
```

```agda
record Model {s} (Sg : Sign s) : Type (o ⊔ ℓ ⊔ s) where
  no-eta-equality
  field
    ob : ∣ Sort Sg ∣ → Ob

  obs : List ∣ Sort Sg ∣ → Ob
  obs Γ = tensor-list ob Γ

  field
    mor : ∀ Γ X → ∣ Op Sg Γ X ∣ → Hom (obs Γ) (ob X)

{-# DISPLAY Model.obs Γ = tensor-list Model.ob Γ #-}

open Model
```

## Homomorphisms

```agda
record Homomorphism {s} {Sg : Sign s} (A B : Model Sg) : Type (ℓ ⊔ s) where
  no-eta-equality
  constructor model-hom
  field
    ⟦_⟧ₕ : ∀ X → Hom (A .ob X) (B .ob X)
    preserves : ∀ Γ X op → ⟦_⟧ₕ X ∘ A .mor Γ X op ≡ B .mor Γ X op ∘ tensor-hom ⟦_⟧ₕ Γ

open Homomorphism

homomorphism-path : ∀ {s} {Sg : Sign s}
                  → {A B : Model Sg} {ϕ ψ : Homomorphism A B}
                  → (∀ X → ⟦ ϕ ⟧ₕ X ≡ ⟦ ψ ⟧ₕ X)
                  → ϕ ≡ ψ
homomorphism-path p i .⟦_⟧ₕ X = p X i
homomorphism-path {A = A} {B = B} {ϕ = ϕ} {ψ = ψ} p i .preserves Γ X op =
  is-prop→pathp
    (λ i → Hom-set _ _ (p X i ∘ A .mor Γ X op) (B .mor Γ X op ∘ tensor-hom (λ X → p X i) Γ))
    (ϕ .preserves Γ X op) (ψ .preserves Γ X op) i
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Homomorphism)
Homomorphism-is-hlevel : ∀ {s} {Sg : Sign s} {A B : Model Sg} → (n : Nat)
                       → is-hlevel (Homomorphism A B) (2 + n)
Homomorphism-is-hlevel n =
  Iso→is-hlevel (2 + n) eqv hlevel!

instance
  H-Level-homomorphism : ∀ {s} {Sg : Sign s} {A B : Model Sg} {n}
                       → H-Level (Homomorphism A B) (2 + n)
  H-Level-homomorphism = basic-instance 2 (Homomorphism-is-hlevel 0)
```
-->


## Categories of Models

```agda
Models : ∀ {s} → (Sg : Sign s) → Precategory (o ⊔ ℓ ⊔ s) (ℓ ⊔ s)
Models Sg .Precategory.Ob = Model Sg
Models Sg .Precategory.Hom = Homomorphism
Models Sg .Precategory.Hom-set _ _ = hlevel!
Models Sg .Precategory.id {A} =
  model-hom (λ _ → id) path where abstract
    path : ∀ Γ X op → id ∘ A .mor Γ X op ≡ A .mor Γ X op ∘ tensor-hom (λ _ → id) Γ
    path Γ X op = idl _ ∙ intror (tensor-hom-id Γ)
Models Sg .Precategory._∘_ {A} {B} {C} f g =
  model-hom (λ X →  ⟦ f ⟧ₕ X ∘ ⟦ g ⟧ₕ X) path where abstract
    path : ∀ Γ X op
         → (⟦ f ⟧ₕ X ∘ ⟦ g ⟧ₕ X) ∘ A .mor Γ X op
         ≡ C .mor Γ X op ∘ tensor-hom (λ X → ⟦ f ⟧ₕ X ∘ ⟦ g ⟧ₕ X) Γ
    path Γ X op =
      pullr (g .preserves Γ X op) ··
      pulll (f .preserves Γ X op) ··
      pullr (sym $ tensor-hom-∘ (⟦ f ⟧ₕ) (⟦ g ⟧ₕ) Γ)
Models Sg .Precategory.idr _ = homomorphism-path λ _ → idr _
Models Sg .Precategory.idl _ = homomorphism-path λ _ → idl _
Models Sg .Precategory.assoc _ _ _ = homomorphism-path λ _ → assoc _ _ _
```

