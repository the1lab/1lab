<!--
```agda
open import Cat.Functor.Equivalence.Properties
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Conservative
open import Cat.Instances.Coalgebras
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Comonad
open import Cat.Displayed.Total
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Coalgebras.Colimits {o ℓ} {C : Precategory o ℓ} {F : Functor C C} (W : Comonad-on F) where
```

<!--
```agda
private
  module CoEM = Cat.Reasoning (Coalgebras W)
  module C = Cat.Reasoning C
  module W = Comonad-on W

open Coalgebra-on
open Total-hom
```
-->

# Colimits in categories of coalgebras {defines="colimits-in-categories-of-coalgebras"}

This module dualises the construction of [[limits in categories of algebras]]
for a [[monad]] to [[colimits]] in categories of [[coalgebras]] for a
[[comonad]]; see there for explanations.

<!--
```agda
module _ {jo jℓ} {J : Precategory jo jℓ} (F : Functor J (Coalgebras W)) where
  private
    module J = Precategory J
    module F = Functor F
    module FAlg j = Coalgebra-on (F.₀ j .snd)
    Forget-CoEM = πᶠ (Coalgebras-over W)
  open Functor
  open _=>_
```
-->

```agda
  Forget-CoEM-preserves-colimits : preserves-colimit (πᶠ (Coalgebras-over W)) F
  Forget-CoEM-preserves-colimits = left-adjoint-is-cocontinuous (Forget⊣Cofree W)

  make-coalgebra-colimit
    : ∀ {K : Functor ⊤Cat C} {eta : Forget-CoEM F∘ F => K F∘ !F}
    → (colim : is-lan !F (Forget-CoEM F∘ F) K eta)
    → (rho : Coalgebra-on W (K .F₀ tt))
    → (∀ j → W.W₁ (is-colimit.ψ colim j) C.∘ FAlg.ρ j ≡ rho .ρ C.∘ is-colimit.ψ colim j)
    → make-is-colimit F (K .F₀ tt , rho)
  make-coalgebra-colimit colim apex-coalg comm = coem-colim where
    module colim = is-colimit colim
    open make-is-colimit
    module apex = Coalgebra-on apex-coalg
    open _=>_
    coem-colim : make-is-colimit F _
    coem-colim .ψ j .hom = colim.ψ j
    coem-colim .ψ j .preserves = comm j
    coem-colim .commutes f    = ext (colim.commutes f)
    coem-colim .universal eta p .hom =
      colim.universal (λ j → eta j .hom) (λ f i → p f i .hom)
    coem-colim .factors eta p =
      ext (colim.factors _ _)
    coem-colim .unique eta p other q =
      ext (colim.unique _ _ _ λ j i → q j i .hom)
    coem-colim .universal eta p .preserves = colim.unique₂ (λ j → W.W₁ (eta j .hom) C.∘ F.F₀ j .snd .ρ)
      (λ f → C.pullr (sym (F.F₁ f .preserves))
           ∙ C.pulll (sym (W.W-∘ _ _) ∙ ap W.W₁ (ap hom (p f))))
      (λ j → C.pullr (sym (comm j))
           ∙ C.pulll (sym (W.W-∘ _ _) ∙ ap W.W₁ (colim.factors _ _)))
      (λ j → C.pullr (colim.factors _ _)
           ∙ sym (eta j .preserves))

  Forget-lift-colimit : Colimit (Forget-CoEM F∘ F) → Colimit F
  Forget-lift-colimit colim-over = to-colimit $ to-is-colimit $ make-coalgebra-colimit
    (Colimit.has-colimit colim-over) coapex-coalgebra (λ j → sym (colim-over.factors _ _))
    where
    module colim-over = Colimit colim-over
    module colim = Lan colim-over

    coapex-coalgebra : Coalgebra-on W colim-over.coapex
    coapex-coalgebra .ρ =
      colim-over.universal (λ j → W.W₁ (colim-over.ψ j) C.∘ FAlg.ρ j) comm where abstract
      comm : ∀ {x y} (f : J.Hom x y)
           → (W.W₁ (colim-over.ψ y) C.∘ FAlg.ρ y) C.∘ F.₁ f .hom
          ≡ W.W₁ (colim-over.ψ x) C.∘ FAlg.ρ x
      comm {x} {y} f =
        (W.W₁ (colim-over.ψ y) C.∘ FAlg.ρ y) C.∘ F.₁ f .hom      ≡⟨ C.pullr (sym (F.₁ f .preserves)) ⟩
        W.W₁ (colim-over.ψ y) C.∘ W.W₁ (F.₁ f .hom) C.∘ FAlg.ρ x ≡⟨ C.pulll (sym (W.W-∘ _ _)) ⟩
        W.W₁ (colim-over.ψ y C.∘ F.₁ f .hom) C.∘ FAlg.ρ x        ≡⟨ ap W.W₁ (colim-over.commutes f) C.⟩∘⟨refl ⟩
        W.W₁ (colim-over.ψ x) C.∘ FAlg.ρ x                       ∎
    coapex-coalgebra .ρ-counit = colim-over.unique₂ _ colim-over.commutes
      (λ j → C.pullr (colim-over.factors _ _)
          ∙∙ C.pulll (W.counit.is-natural _ _ _)
          ∙∙ C.cancelr (FAlg.ρ-counit j))
      (λ j → C.idl _)
    coapex-coalgebra .ρ-comult = colim-over.unique₂ _
      (λ f → C.pullr $ C.pullr (sym (F.₁ f .preserves))
           ∙ C.pulll (sym (W.W-∘ _ _) ∙ ap W.W₁ (colim-over.commutes f)))
      (λ j → C.pullr (colim-over.factors _ _)
           ∙ sym (C.pulll (sym (W.W-∘ _ _) ∙ ap W.W₁ (colim-over.factors _ _) ∙ W.W-∘ _ _)
               ∙∙ C.extendr (sym (FAlg.ρ-comult j))
               ∙∙ ap (C._∘ FAlg.ρ j) (sym (W.comult.is-natural _ _ _))
                ∙ sym (C.assoc _ _ _)))
      (λ j → C.pullr (colim-over.factors _ _))
```

<!--
```agda
module _ {jo jℓ} {J : Precategory jo jℓ} where
  open lifts-colimit
  open creates-colimit
```
-->

```agda
  Forget-CoEM-lifts-colimits : lifts-colimits-of J (πᶠ (Coalgebras-over W))
  Forget-CoEM-lifts-colimits colim .lifted = Forget-lift-colimit _ colim
  Forget-CoEM-lifts-colimits colim .preserved =
    Forget-CoEM-preserves-colimits _ (Lan.has-lan (Forget-lift-colimit _ colim))

  Forget-CoEM-creates-colimits : creates-colimits-of J (πᶠ (Coalgebras-over W))
  Forget-CoEM-creates-colimits = conservative+lifts→creates-colimits
    Forget-CoEM-is-conservative Forget-CoEM-lifts-colimits
```

```agda
Eilenberg-Moore-is-cocomplete
  : ∀ {a b} → is-cocomplete a b C → is-cocomplete a b (Coalgebras W)
Eilenberg-Moore-is-cocomplete = lifts-colimits→cocomplete
  (πᶠ (Coalgebras-over W)) Forget-CoEM-lifts-colimits
```
