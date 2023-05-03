<!--
```agda
-- {-# OPTIONS --lossy-unification #-}
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Morphism.Factorisation
open import Cat.Morphism.StrongEpi
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Instances.Slice
open import Cat.Diagram.Image
open import Cat.Prelude
open import Cat.Regular

import Cat.Displayed.Instances.Subobjects
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Regular.Image
  {o ℓ} {C : Precategory o ℓ}
  (reg : is-regular C)
  where
```

<!--
```agda
open Binary-products C (reg .is-regular.lex.products)
open Cat.Displayed.Instances.Subobjects C
open is-regular reg
open Factorisation
open Pullback
open /-Hom
open /-Obj
open Cr C
```
-->

# Images in regular categories

```agda
Im : ∀ {x y} (f : Hom x y) → Subobject y
Im f .domain = _
Im f .map    = factor f .forget
Im f .monic  = out! (factor f .forget∈M)

Im-universal
  : ∀ {x y o} (f : Hom x y)
  → (m : o ↪ y) {e : Hom x o}
  → f ≡ m .mor ∘ e
  → Im f ≤ₘ cutₛ (m .monic)
Im-universal f m {e = e} p = r where
  the-lift = out! {pa = is-strong-epi-is-prop C _} (factor f .mediate∈E) .snd
    m (sym (factor f .factors) ∙ p)

  r : _ ≤ₘ _
  r .map = the-lift .centre .fst
  r .sq  = idl _ ∙ sym (the-lift .centre .snd .snd)
```

```agda
image-pre-cover
  : ∀ {a b c}
  → (f : Hom b c)
  → (g : Hom a b)
  → is-strong-epi C g
  → (Im f) Sub.≅ (Im (f ∘ g))
image-pre-cover {a = a} {b} {c} f g g-covers = Sub-antisym imf≤imfg imfg≤imf where
  imfg≤imf : Im (f ∘ g) ≤ₘ Im f
  imfg≤imf = Im-universal _ (record { monic = Im f .monic }) (pushl (factor f .factors))

  the-lift : Σ (Hom b im[ f ∘ g ]) _
  the-lift =
    g-covers .snd
      (≤ₘ→mono imfg≤imf)
      {factor (f ∘ g) .mediate}
      {factor f .mediate}
      (out! (factor f .forget∈M) _ _ (sym (pulll (sym (imfg≤imf .sq) ∙ idl _) ∙ sym (factor (f ∘ g) .factors) ∙ pushl (factor f .factors)))) .centre

  inverse : is-invertible (imfg≤imf .map)
  inverse = is-strong-epi→is-extremal-epi C (out! {pa = is-strong-epi-is-prop C _} (factor f .mediate∈E))
    (≤ₘ→mono imfg≤imf) (the-lift .fst) (sym (the-lift .snd .snd))

  imf≤imfg : Im f ≤ₘ Im (f ∘ g)
  imf≤imfg .map = inverse .is-invertible.inv
  imf≤imfg .sq = invertible→epic inverse _ _ $
    pullr (sym (imfg≤imf .sq) ∙ idl _)
    ∙ sym (cancelr (inverse .is-invertible.invr) ∙ introl refl)
```
