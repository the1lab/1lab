<!--
```agda
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Coproduct
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Prelude

open import Data.Sum

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Instances.Presheaf.Colimits {o ℓ} (κ : Level) (C : Precategory o ℓ) where
```

# Colimits in presheaf categories

Just like [[limits in presheaf categories]], these are computed
pointwise as colimits in $\Sets$. Therefore, this page is only lightly
commented.

<!--
```agda
open Functor
open Cat C
open _=>_

private module PSh = Cat (PSh κ C)
```
-->

```agda
⊥PSh : ⌞ PSh κ C ⌟
⊥PSh .F₀ x = el! (Lift κ ⊥)
⊥PSh .F₁ _ ()
⊥PSh .F-id = ext λ ()
⊥PSh .F-∘ _ _ = ext λ ()

PSh-initial : Initial (PSh κ C)
PSh-initial = record { has⊥ = uniq } where
  uniq : is-initial (PSh κ C) ⊥PSh
  uniq x .centre .η _ ()
  uniq x .centre .is-natural _ _ _ = ext λ ()
  uniq x .paths f = ext λ _ ()

_⊎PSh_ : (A B : PSh.Ob) → PSh.Ob
(A ⊎PSh B) .F₀ i = el! (∣ A .F₀ i ∣ ⊎ ∣ B .F₀ i ∣)
(A ⊎PSh B) .F₁ h (inl x) = inl (A .F₁ h x)
(A ⊎PSh B) .F₁ h (inr x) = inr (B .F₁ h x)
(A ⊎PSh B) .F-id = funext λ where
  (inl x) → ap inl (A .F-id $ₚ x)
  (inr x) → ap inr (B .F-id $ₚ x)
(A ⊎PSh B) .F-∘ f g = funext λ where
  (inl x) → ap inl (A .F-∘ f g $ₚ x)
  (inr x) → ap inr (B .F-∘ f g $ₚ x)

PSh-coproducts : (A B : PSh.Ob) → Coproduct (PSh κ C) A B
PSh-coproducts A B = coprod where
  open Coproduct
  open is-coproduct
  module A = Functor A
  module B = Functor B

  ι₁' : A => (A ⊎PSh B)
  ι₁' .η _ x = inl x
  ι₁' .is-natural x y f i a = inl (A.₁ f a)

  ι₂' : B => (A ⊎PSh B)
  ι₂' .η _ x = inr x
  ι₂' .is-natural x y f i b = inr (B.₁ f b)

  coprod : Coproduct (PSh _ C) A B
  coprod .coapex = A ⊎PSh B
  coprod .ι₁ = ι₁'
  coprod .ι₂ = ι₂'
  coprod .has-is-coproduct .is-coproduct.[_,_] f g .η _ (inl x) = f .η _ x
  coprod .has-is-coproduct .is-coproduct.[_,_] f g .η _ (inr x) = g .η _ x
  coprod .has-is-coproduct .is-coproduct.[_,_] f g .is-natural x y h = funext λ where
    (inl x) → f .is-natural _ _ _ $ₚ _
    (inr x) → g .is-natural _ _ _ $ₚ _
  coprod .has-is-coproduct .[]∘ι₁ = trivial!
  coprod .has-is-coproduct .[]∘ι₂ = trivial!
  coprod .has-is-coproduct .unique p q = ext λ where
    a (inl x) → unext p a x
    a (inr x) → unext q a x

PSh-coequaliser
  : ∀ {X Y} (f g : PSh.Hom X Y)
  → Coequaliser (PSh κ C) f g
PSh-coequaliser {X = X} {Y = Y} f g = coequ where
  open Coequaliser
  open is-coequaliser
  module X = Functor X
  module Y = Functor Y

  incq : ∀ {i} → _ → Coeq (f .η i) (g .η i)
  incq = inc

  coequ : Coequaliser (PSh _ C) f g
  coequ .coapex .F₀ i = el (Coeq (f .η i) (g .η i)) squash
  coequ .coapex .F₁ h = Coeq-rec (λ g → inc (Y.₁ h g)) λ x →
    inc (Y.₁ h (f .η _ x)) ≡˘⟨ ap incq (happly (f .is-natural _ _ h) x) ⟩
    inc (f .η _ _)         ≡⟨ glue (X.₁ h x) ⟩
    inc (g .η _ _)         ≡⟨ ap incq (happly (g .is-natural _ _ h) x) ⟩
    inc (Y.₁ h (g .η _ x)) ∎
  coequ .coapex .F-id = ext λ _ → ap incq (happly Y.F-id _)
  coequ .coapex .F-∘ f g = ext λ _ → ap incq (happly (Y.F-∘ f g) _)
  coequ .coeq .η i = incq
  coequ .coeq .is-natural x y f = refl
  coequ .has-is-coeq .coequal = ext λ i x → glue x
  coequ .has-is-coeq .universal {F = F} {e' = e'} p .η x =
    Coeq-rec (e' .η x) (p ηₚ x $ₚ_)
  coequ .has-is-coeq .universal {F = F} {e' = e'} p .is-natural x y f = ext λ x →
    e' .is-natural _ _ _ $ₚ _
  coequ .has-is-coeq .factors = trivial!
  coequ .has-is-coeq .unique {F = F} p = reext! p
```
