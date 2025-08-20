---
description: |

---
<!--
```agda
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Displayed.Instances.Slice
open import Cat.Diagram.Product
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Slice.Properties where
```

# Properties of slice categories

This module gathers together some useful properties of [[slice categories]].

<!--
```agda
module _
  {o ℓ}
  {B : Precategory o ℓ}
  where
  open Cat.Reasoning B
  open /-Obj
  open Slice-hom
```
-->

## Total products in slice categories

A [[total product]] in a slice category is given by a [[product]] of
the domains of the slices.

```agda
  slice-total-product
    : ∀ {I J X Y} {f : Hom X I} {g : Hom Y J}
    → (X×Y : Product B X Y)
    → (I×J : Product B I J)
    → ProductP (Slices B) I×J (cut f) (cut g)
  slice-total-product {f = f} {g = g} X×Y I×J = total-prod where
    open is-product-over
    open ProductP

    module X×Y = Product X×Y
    module I×J = Product I×J

    total-prod : ProductP (Slices B) I×J (cut f) (cut g)
    total-prod .apex' .dom = X×Y.apex
    total-prod .apex' .map = I×J.⟨ f ∘ X×Y.π₁ , g ∘ X×Y.π₂ ⟩
    total-prod .π₁' .map = X×Y.π₁
    total-prod .π₁' .com = sym I×J.π₁∘⟨⟩
    total-prod .π₂' .map = X×Y.π₂
    total-prod .π₂' .com = sym I×J.π₂∘⟨⟩
```

The universal property follows from a bit of routine algebra involving
products.

```agda
    total-prod .has-is-product' .⟨_,_⟩' f g .map = X×Y.⟨ f .map , g .map ⟩
    total-prod .has-is-product' .⟨_,_⟩' f g .com = sym $ I×J.unique₂
      (pulll I×J.π₁∘⟨⟩ ∙ sym (f .com))
      (pulll I×J.π₂∘⟨⟩ ∙ sym (g .com))
      (pulll I×J.π₁∘⟨⟩ ∙ pullr X×Y.π₁∘⟨⟩)
      (pulll I×J.π₂∘⟨⟩ ∙ pullr X×Y.π₂∘⟨⟩)
    total-prod .has-is-product' .π₁∘⟨⟩' = Slice-pathp X×Y.π₁∘⟨⟩
    total-prod .has-is-product' .π₂∘⟨⟩' = Slice-pathp X×Y.π₂∘⟨⟩
    total-prod .has-is-product' .unique' p q = Slice-pathp $
      X×Y.unique (λ i → p i .map) (λ i → q i .map)
```
