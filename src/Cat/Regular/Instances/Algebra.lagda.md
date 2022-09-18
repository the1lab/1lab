```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Monad.Limits
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Prelude
open import Cat.Regular

import Cat.Diagram.Monad as Mon

module Cat.Regular.Instances.Algebra {ℓ} (M : Mon.Monad (Sets ℓ)) where
```

<!--
```agda
open Mon (Sets ℓ)
private module M = Monad M
private module Setsᴹ = Precategory (Eilenberg-Moore M)
open Algebra-hom
open Algebra-on
open is-regular
open Finitely-complete
open Pullback
open is-pullback
open Terminal
open Coequaliser
open is-coequaliser
```
-->

```agda
Eilenberg-Moore-is-lex : Finitely-complete (Eilenberg-Moore M)
Eilenberg-Moore-is-lex = with-pullbacks (Eilenberg-Moore M) term pb
  where
    term : Terminal (Eilenberg-Moore M)
    term .top = el (Lift _ ⊤) (λ x y p q i j → lift tt) , record
      { ν      = λ _ → lift tt
      ; ν-unit = refl
      ; ν-mult = refl
      }
    term .has⊤ x = contr
      (record { morphism = λ _ → lift tt ; commutes = refl })
      (λ x → Algebra-hom-path refl)

    pb : ∀ {A B X : Algebra M} (f : Algebra-hom M A X) (g : Algebra-hom M B X)
       → Pullback (Eilenberg-Moore M) f g
    pb {A} {B} {X} f g .apex = set , alg
      where
        set : Set _
        set .∣_∣ = Σ ⌞ A ⌟ λ x → Σ ⌞ B ⌟ λ y → f .morphism x ≡ g .morphism y
        set .is-tr = hlevel!

        νpb : ∣ M.M₀ set ∣ → ∣ set ∣
        νpb m0 = A .snd .ν (M.M₁ fst m0) , B .snd .ν (M.M₁ (λ x → x .snd .fst) m0)
               , pres
          where abstract
          pres : f .morphism (A .snd .ν (M.M₁ fst m0))
               ≡ g .morphism (B .snd .ν (M.M₁ (λ x → x .snd .fst) m0))
          pres =
            (f .commutes $ₚ _)
            ∙ ap (X .snd .ν) ((sym (M.M-∘ _ _) $ₚ _) ·· (ap M.M₁ (funext λ x → x .snd .snd) $ₚ m0) ·· ((M.M-∘ _ _) $ₚ _))
            ∙ sym (g .commutes $ₚ M.M₁ (λ x → x .snd .fst) m0)

        alg : Algebra-on M _
        alg .ν = νpb
        alg .ν-unit = funext λ where
          (x , y , p) → Σ-pathp
            (ap (A .snd .ν) (sym (M.unit.is-natural _ _ _ $ₚ _)) ∙ (A .snd .ν-unit $ₚ x)) $
            Σ-pathp-dep
              (ap (B .snd .ν) (sym (M.unit.is-natural _ _ _ $ₚ _)) ∙ (B .snd .ν-unit $ₚ y))
              (is-prop→pathp (λ _ → X .fst .is-tr _ _) _ _)
        alg .ν-mult = funext λ where
          x → Σ-pathp
            ( ap (A .snd .ν) ((sym (M.M-∘ _ _) $ₚ _) ∙ ((M.M-∘ _ _) $ₚ _))
            ∙ (A .snd .ν-mult $ₚ _)
            ∙ ap (A .snd .ν) (M.mult.is-natural _ _ _ $ₚ _))
            (Σ-pathp-dep
              (( ap (B .snd .ν) ((sym (M.M-∘ _ _) $ₚ _) ∙ ((M.M-∘ _ _) $ₚ _))
               ∙ (B .snd .ν-mult $ₚ _)
               ∙ ap (B .snd .ν) (M.mult.is-natural _ _ _ $ₚ _)))
              (is-prop→pathp (λ _ → X .fst .is-tr _ _) _ _))
    pb f g .p₁ .morphism (x , _ , _) = x
    pb f g .p₁ .commutes = refl
    pb f g .p₂ .morphism (_ , y , _) = y
    pb f g .p₂ .commutes = refl
    pb f g .has-is-pb .square = Algebra-hom-path (funext λ { (_ , _ , p) → p })

    pb f g .has-is-pb .limiting {p₁' = p₁'} {p₂' = p₂'} sq′ .morphism x =
      p₁' .morphism x , p₂' .morphism x , ap (λ e → e .morphism x) sq′
    pb {A} {B} {X} f g .has-is-pb .limiting {p₁' = p₁'} {p₂' = p₂'} sq′
      .commutes = funext λ x →
        Σ-pathp
          ((p₁' .commutes $ₚ x) ∙ ap (A .snd .ν) (M.M-∘ fst _ $ₚ _))
          (Σ-pathp-dep
            ( (p₂' .commutes $ₚ x)
            ∙ ap (B .snd .ν) (M.M-∘ (λ x → x .snd .fst) _ $ₚ _))
            (is-prop→pathp (λ _ → X .fst .is-tr _ _) _ _))

    pb f g .has-is-pb .p₁∘limiting = Algebra-hom-path refl
    pb f g .has-is-pb .p₂∘limiting = Algebra-hom-path refl
    pb {X = X} f g .has-is-pb .unique p q = Algebra-hom-path $
      funext λ x → Σ-pathp (ap morphism p $ₚ x) $
        Σ-pathp-dep (ap morphism q $ₚ x) $
          is-prop→pathp (λ i → X .fst .is-tr _ _) _ _

{-
Eilenberg-Moore-is-regular : is-regular (Eilenberg-Moore M)
Eilenberg-Moore-is-regular = go where
  go : is-regular (Eilenberg-Moore M)
  go .has-is-lex = is-complete→finitely _ $
    Eilenberg-Moore-is-complete $ Sets-is-complete {ℓ} {ℓ} {ℓ}
  go .kernel-pair-coeq {d} {c} f = the-coeq where
    nadir : Algebra M
    nadir .fst .∣_∣ = Σ _ λ y → ∥ fibre (f .morphism) y ∥
    nadir .fst .is-tr = hlevel!
    nadir .snd .ν m0 =
        (c .snd .ν $ M.M₁ fst m0)
      , {!   !}
    nadir .snd .ν-unit = {!   !}
    nadir .snd .ν-mult = {!   !}

    the-coeq : Coequaliser (Eilenberg-Moore M) _ _
    the-coeq .coapex = nadir
    the-coeq .coeq .morphism x = f .morphism x , inc (x , refl)
    the-coeq .coeq .commutes = funext λ x →
      Σ-prop-path (λ _ → squash) ((f .commutes $ₚ _) ∙ {!   !})
    the-coeq .has-is-coeq = {!   !}
  go .regular-epi-stability = {!   !}
  -}
```
