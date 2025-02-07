open import 1Lab.Prelude hiding (_∘_ ; id ; _↪_ ; _↠_)

open import Cat.Morphism
open import Cat.Base

open Precategory

module Cat.Morphism.Instances where

abstract
  instance
    H-Level-is-invertible
      : ∀ {o ℓ} {C : Precategory o ℓ} {a b} {f : C .Hom a b} {n} → H-Level (is-invertible C f) (suc n)
    H-Level-is-invertible {C = C} = prop-instance (is-invertible-is-prop C)

  unquoteDecl H-Level-↪        = declare-record-hlevel 2 H-Level-↪ (quote _↪_)
  unquoteDecl H-Level-↠        = declare-record-hlevel 2 H-Level-↠ (quote _↠_)
  unquoteDecl H-Level-Inverses = declare-record-hlevel 2 H-Level-Inverses (quote Inverses)
  unquoteDecl H-Level-≅        = declare-record-hlevel 2 H-Level-≅ (quote _≅_)
  unquoteDecl
    H-Level-has-section = declare-record-hlevel 2 H-Level-has-section (quote has-section)
  unquoteDecl
    H-Level-has-retract = declare-record-hlevel 2 H-Level-has-retract (quote has-retract)

module _ {o ℓ} {C : Precategory o ℓ} where instance
  Extensional-↪ : ∀ {a b ℓr} ⦃ _ : Extensional (C .Hom a b) ℓr ⦄ → Extensional (_↪_ C a b) ℓr
  Extensional-↪ ⦃ sa ⦄ = injection→extensional! (↪-pathp C) sa

  Extensional-↠ : ∀ {a b ℓr} ⦃ _ : Extensional (C .Hom a b) ℓr ⦄ → Extensional (_↠_ C a b) ℓr
  Extensional-↠ ⦃ sa ⦄ = injection→extensional! (↠-pathp C) sa

  Extensional-≅ : ∀ {a b ℓr} ⦃ _ : Extensional (C .Hom a b) ℓr ⦄ → Extensional (_≅_ C a b) ℓr
  Extensional-≅ ⦃ sa ⦄ = injection→extensional! (≅-pathp C refl refl) sa

  Funlike-≅
    : ∀ {ℓ' ℓ''} {A : Type ℓ'} {B : A → Type ℓ''}
    → ∀ {a b} ⦃ i : Funlike (Hom C a b) A B ⦄
    → Funlike (_≅_ C a b) A B
  Funlike-≅ .Funlike._#_ f x = f .to # x
