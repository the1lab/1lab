```agda
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Functor.Kan.Pointwise where
```

# Pointwise Kan Extensions

<!--
```agda
module _
  {o o′ ℓ ℓ′}
  {C : Precategory ℓ ℓ} {C' : Precategory o ℓ} {D : Precategory o′ ℓ′}
  (F : Functor C C') (G : Functor C D)
  where

  private
    module C = Cat.Reasoning C
    module C' = Cat.Reasoning C'
    module D = Cat.Reasoning D
    open Func
    open ↓Obj
    open ↓Hom
    open _=>_
    open Lan
    open is-lan
```
-->

```agda
  cocomplete→lan
    : is-cocomplete ℓ ℓ D
    → Lan F G
  cocomplete→lan colimits = lan module cocomplete→lan where
      open Lan
      open is-lan

      Dia : (c' : C'.Ob) → Functor (F ↘ c') D
      Dia c' = G F∘ Dom F (Const c')

      module ↓colim c' = Colimit (colimits (Dia c'))

      F′ : Functor C' D
      F′ .F₀ c' = ↓colim.coapex c'
      F′ .F₁ f =
        ↓colim.universal _
          (λ j → ↓colim.ψ _ (↓obj (f C'.∘ j .map)))
          (λ f →
            ↓colim.commutes _ (↓hom {β = f .β} (C'.pullr (f .sq)
            ·· C'.elim-inner refl
            ·· sym (C'.idl _))))
      F′ .F-id =
        sym $ ↓colim.unique _ _ _ _ λ j →
          D.idl _
          ∙ ap (↓colim.ψ _) (↓Obj-path _ _ refl refl (sym (C'.idl _)))
      F′ .F-∘ f g =
        sym $ ↓colim.unique _ _ _ _ λ j →
          D.pullr (↓colim.factors _ _ _)
          ∙ ↓colim.factors _ _ _
          ∙ ap (↓colim.ψ _) (↓Obj-path _ _ refl refl (C'.assoc _ _ _))

      lan : Lan F G
      lan .Ext = F′
      lan .eta .η c = ↓colim.ψ (F .F₀ c) (↓obj C'.id)
      lan .eta .is-natural x y f =
        ↓colim.commutes (F₀ F y) (↓hom (ap (C'.id C'.∘_) (sym (C'.idr _))))
        ∙ sym (↓colim.factors _ _ _)
      lan .has-lan .σ {M = M} α .η c' =
        ↓colim.universal c'
          (λ j → M .F₁ (j .map) D.∘ α .η (j .x))
          (λ f →
            D.pullr (α .is-natural _ _ _)
            ∙ pulll M ((f .sq) ∙ C'.idl _))
      lan .has-lan .σ {M = M} α .is-natural x y f =
        ↓colim.unique₂ _ _
          (λ f →
            D.pullr (α .is-natural _ _ _)
            ∙ pulll M (C'.pullr (f .sq) ∙ C'.elim-inner refl))
          (λ j →
            D.pullr (↓colim.factors _ _ _)
            ∙ ↓colim.factors _ _ _)
          (λ j →
            D.pullr (↓colim.factors _ _ _)
            ∙ D.pulll (sym (M .F-∘ _ _)))
      lan .has-lan .σ-comm {M = M} = Nat-path λ c →
        ↓colim.factors _ _ _
        ∙ D.eliml (M .F-id)
      lan .has-lan .σ-uniq {M = M} {α = α} {σ′ = σ′} p = Nat-path λ c' →
        sym $ ↓colim.unique _ _ _ _ λ j →
          σ′ .η c' D.∘ ↓colim.ψ c' j                                ≡⟨ ap (λ ϕ → σ′ .η c' D.∘ ↓colim.ψ c' ϕ) (↓Obj-path _ _ refl refl (sym (C'.idr _))) ⟩
          (σ′ .η c' D.∘ ↓colim.ψ c' (↓obj (j .map C'.∘ C'.id)))     ≡⟨ D.pushr (sym $ ↓colim.factors _ _ _) ⟩
          (σ′ .η c' D.∘ ↓colim.universal _ _ _) D.∘ ↓colim.ψ _ _    ≡⟨ D.pushl (σ′ .is-natural _ _ _) ⟩
          M .F₁ (j .map) D.∘ (σ′ .η _ D.∘ ↓colim.ψ _ (↓obj C'.id))  ≡˘⟨ (D.refl⟩∘⟨ (p ηₚ j .x)) ⟩
          M .F₁ (j .map) D.∘ α .η (j .x)                            ∎
```

```agda
  ff→pointwise-lan-ext
    : (cocompl : is-cocomplete ℓ ℓ D)
    → is-fully-faithful F
    → natural-iso (cocomplete→lan cocompl .Ext F∘ F) G
  ff→pointwise-lan-ext cocompl ff = (to-natural-iso ni) ni⁻¹ where
    open cocomplete→lan cocompl
    open make-natural-iso
    module ff {x} {y} = Equiv (_ , ff {x} {y})

    ni : make-natural-iso G (F′ F∘ F)
    ni .eta x =
      ↓colim.ψ _ (↓obj C'.id)
    ni .inv x =
      ↓colim.universal _
        (λ j → G .F₁ (ff.from (j .map)))
        (λ f →
          collapse G $
          fully-faithful→faithful {F = F} ff $
          F .F-∘ _ _
          ·· ap₂ C'._∘_ (ff.ε _) refl
          ·· f .sq
          ·· C'.idl _
          ·· sym (ff.ε _))
    ni .eta∘inv x =
      ↓colim.unique₂ _ _
        (λ f →
          ↓colim.commutes _ f)
        (λ j →
          D.pullr (↓colim.factors _ _ _)
          ∙ ↓colim.commutes _ (↓hom (ap₂ C'._∘_ refl (ff.ε _))))
        (λ j → D.idl _)
    ni .inv∘eta x =
      ↓colim.factors _ _ _
      ∙ elim G (ap ff.from (sym (F .F-id)) ∙ ff.η _)
    ni .natural x y f =
      ↓colim.factors _ _ _
      ∙ sym (↓colim.commutes _ (↓hom (ap₂ C'._∘_ refl (sym (C'.idr _)))))
```
