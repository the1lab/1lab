<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Pushout.Properties
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Colimit.Finite
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Morphism.Strong.Epi
open import Cat.Diagram.Coproduct
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Diagram.Pushout
open import Cat.Prelude

open import Data.Set.Surjection
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
open Pushout
open Coequaliser
open is-coequaliser
open is-regular-epi

private
  module C = Cat C
  module PSh = Cat (PSh κ C)
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
  coprod .has-is-coproduct .[]∘ι₁ = ext λ _ _ → refl
  coprod .has-is-coproduct .[]∘ι₂ = ext λ _ _ → refl
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
  coequ .has-is-coeq .factors = ext λ _ _ → refl
  coequ .has-is-coeq .unique {F = F} p = reext! p

PSh-finitely-cocomplete : Finitely-cocomplete (PSh κ C)
PSh-finitely-cocomplete = with-coequalisers (PSh κ C) PSh-initial PSh-coproducts PSh-coequaliser

PSh-pushouts : ∀ {F G H} (α : F => G) (β : F => H) → Pushout (PSh κ C) α β
PSh-pushouts = PSh-finitely-cocomplete .Finitely-cocomplete.pushouts
```
<!--
```agda
PSh-cocomplete : is-cocomplete κ κ (PSh κ C)
PSh-cocomplete = Functor-cat-is-cocomplete $ Sets-is-cocomplete {ι = κ} {κ} {κ}
```
-->

# Epimorphisms in presheaf categories

```agda
-- https://stacks.math.columbia.edu/tag/00v5
is-epic→is-epic-at : ∀ {F G : ⌞ PSh κ C ⌟} {ε : F => G} → PSh.is-epic ε → ∀ {i} → Cat.is-epic (Sets κ) {a = F .F₀ i} {b = G .F₀ i} (ε .η i)
is-epic→is-epic-at {F = F} {G} {ε} m-epic {i} {c}= epi {c = c} where
  H = PSh-pushouts ε ε .coapex

  ι₁ : G => H
  ι₁ = PSh-pushouts ε ε  .i₁

  ι₂ : G => H
  ι₂ = PSh-pushouts ε ε  .i₂

  p' : ι₁ ≡ ι₂
  p' = m-epic ι₁ ι₂ $ PSh-pushouts ε ε .square

  epi : Cat.is-epic (Sets κ) {a = F .F₀ i} {b = G .F₀ i} (ε .η i)
  epi {c} = injections-eq→is-epic (Sets-pushouts {A = G .F₀ i} {B = G .F₀ i} {C = F .F₀ i} (ε .η i) (ε .η i) .has-is-po) (p' ηₚ i) {c = c}

is-epic→is-regular-epi-at : ∀ {X Y : ⌞ PSh κ C ⌟} {m : X => Y} → PSh.is-epic m → ∀ {i} → is-regular-epi (Sets κ) {X .F₀ i} {Y .F₀ i} (m .η i)
is-epic→is-regular-epi-at {X} {Y} m {i} = surjective→regular-epi _ _ _ $ epi→surjective (X .F₀ i) (Y .F₀ i) _ $ λ { {c} → is-epic→is-epic-at m {c = c} }
```

<!--
```agda
module _ {F G : ⌞ PSh κ C ⌟} {ε : F => G} (ε-epic : PSh.is-epic ε) where
  private
    module F = Functor F
    module G = Functor G

    pr : (i : ⌞ C ⌟) → is-regular-epi (Sets κ) {F.₀ i} {G.₀ i} (ε .η i)
    pr _ = is-epic→is-regular-epi-at ε-epic

    module ε = _=>_ ε
    module pr (i : ⌞ C ⌟) = is-regular-epi (pr i)

    pb-path : ∀ {i} {x y : Σ[ x ∈ F.₀ i ] Σ[ y ∈ F.₀ i ] ε.η i x ≡ ε.η i y}
      → x .fst ≡ y .fst
      → x .snd .fst ≡ y .snd .fst
      → x ≡ y
    pb-path p q i .fst = p i
    pb-path p q i .snd .fst = q i
    pb-path {idx} {x} {y} p q i .snd .snd j =
      is-set→squarep (λ _ _ → G.₀ idx .is-tr)
        (ap (ε .η idx) p) (x .snd .snd) (y .snd .snd) (ap (ε .η idx) q)
        i j
```
-->

```agda
    psh-epi-is-regular : is-regular-epi (PSh κ C) ε
    psh-epi-is-regular .r .F₀ c = pr.r c
    psh-epi-is-regular .r .F₁ {x} {y} f e@(s , r , p) = F ⟪ f ⟫ s , (F ⟪ f ⟫ r) , path where abstract
      path : ε.η y (F.F₁ f s) ≡ ε.η y (F.F₁ f r)
      path = ε.is-natural x y f · s ∙ ap (G.F₁ f) p ∙ sym (ε.is-natural x y f · r)
    psh-epi-is-regular .r .F-id {c} = ext λ s r p → pb-path (F.F-id · s) (F.F-id · r)
    psh-epi-is-regular .r .F-∘ f g = ext λ s r p → pb-path (F.F-∘ _ _ · s) (F.F-∘ _ _ · r)

    psh-epi-is-regular .arr₁ .η x (s , _ , _) = s
    psh-epi-is-regular .arr₁ .is-natural _ _ _ = ext λ _ _ _ → refl
    psh-epi-is-regular .arr₂ .η x (_ , r , _) = r
    psh-epi-is-regular .arr₂ .is-natural _ _ _ = ext λ _ _ _ → refl

    psh-epi-is-regular .has-is-coeq .coequal = ext λ x s r p → p

    psh-epi-is-regular .has-is-coeq .universal {Q} p .η x = pr.universal x {Q .F₀ x} (p ηₚ x)
    psh-epi-is-regular .has-is-coeq .universal {Q} {e'} p .is-natural x y f =  pr.is-regular-epi→is-epic x {c = Q .F₀ y} _ _ $  ext λ s →
      pr.universal y {Q .F₀ y} (p ηₚ y) (G ⟪ f ⟫ ε.η x s)   ≡˘⟨ ap (pr.universal y {Q .F₀ y} (p ηₚ y)) (ε.is-natural x y f · s) ⟩
      pr.universal y {Q .F₀ y} (p ηₚ y) (ε.η y (F ⟪ f ⟫ s)) ≡⟨ pr.factors y {Q .F₀ y} {e' .η y} {p ηₚ y} · (F ⟪ f ⟫ s) ⟩
      e' .η y (F ⟪ f ⟫ s)                                   ≡⟨ e' .is-natural x y f · s ⟩
      Q ⟪ f ⟫ e' .η x s                                     ≡˘⟨ ap (Q ⟪ f ⟫_) (pr.factors x {Q .F₀ x} {e' .η x} {p ηₚ x} · s) ⟩
      Q ⟪ f ⟫ pr.universal x {Q .F₀ x} (p ηₚ x) (ε.η x s)   ∎

    psh-epi-is-regular .has-is-coeq .factors {Q} {e'} {p} = Nat-path λ x → pr.factors x {Q .F₀ x} {e' = e' .η x} {p = p ηₚ x}
    psh-epi-is-regular .has-is-coeq .unique {Q} {e'} {p} {colim} q = Nat-path λ x → pr.unique x {Q .F₀ x} {e' .η x} {p ηₚ x} {colim .η x} (q ηₚ x)
```
