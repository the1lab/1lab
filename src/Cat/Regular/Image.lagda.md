<!--
```agda
-- {-# OPTIONS --lossy-unification #-}
open import Cat.Functor.FullSubcategory
open import Cat.Morphism.Factorisation
open import Cat.Morphism.StrongEpi
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Instances.Slice
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

This module provides tools for working with the [[image factorisation]] of
morphisms in [regular categories], regarded as [subobjects] of the map's
codomain. We start by defining a `Subobject`{.Agda} of $y$ standing for
$\im f$ whenever $f : x \to y$.

[regular categories]: Cat.Regular.html
[subobjects]: Cat.Displayed.Instances.Subobjects.html

```agda
Im : ∀ {x y} (f : Hom x y) → Subobject y
Im f .domain = _
Im f .map    = factor f .forget
Im f .monic  = out! (factor f .forget∈M)
```

We may then use this to rephrase the universal property of $\im f$ as
the initial subobject through which $f$ factors.

```agda
Im-universal
  : ∀ {x y} (f : Hom x y)
  → (m : Subobject y) {e : Hom x (m .domain)}
  → f ≡ m .map ∘ e
  → Im f ≤ₘ m
Im-universal f m {e = e} p = r where
  the-lift = out! {pa = is-strong-epi-is-prop C _} (factor f .mediate∈E) .snd
    record { Subobject m } (sym (factor f .factors) ∙ p)

  r : _ ≤ₘ _
  r .map = the-lift .centre .fst
  r .sq  = idl _ ∙ sym (the-lift .centre .snd .snd)
```

An important fact that will be used in calculating associativity for
[relations in regular categories] is that precomposing with a [strong
epimorphism] preserves images. Intuitively, this is because a strong
epimorphism $a \epi b$ expresses $b$ as a quotient, but this
decomposition does not alter the image of a map $b \to c$.

[strong epimorphism]: Cat.Morphism.StrongEpi.html
[relations in regular categories]: Cat.Bi.Instances.Relations.html

```agda
image-pre-cover
  : ∀ {a b c}
  → (f : Hom b c)
  → (g : Hom a b)
  → is-strong-epi C g
  → (Im f) Sub.≅ (Im (f ∘ g))
image-pre-cover {a = a} {b} {c} f g g-covers = Sub-antisym imf≤imfg imfg≤imf where
  imfg≤imf : Im (f ∘ g) ≤ₘ Im f
  imfg≤imf = Im-universal _ _ (pushl (factor f .factors))

  the-lift : Σ (Hom b im[ f ∘ g ]) _
  the-lift = g-covers .snd
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
