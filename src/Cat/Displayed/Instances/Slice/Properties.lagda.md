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
    → Total-product (Slices B) I×J (cut f) (cut g)
  slice-total-product {f = f} {g = g} X×Y I×J = total-prod where
    open is-total-product
    open Total-product

    module X×Y = Product X×Y
    module I×J = Product I×J

    total-prod : Total-product (Slices B) I×J (cut f) (cut g)
    total-prod .apex' .domain = X×Y.apex
    total-prod .apex' .map = I×J.⟨ f ∘ X×Y.π₁ , g ∘ X×Y.π₂ ⟩
    total-prod .π₁' .to = X×Y.π₁
    total-prod .π₁' .commute = I×J.π₁∘⟨⟩
    total-prod .π₂' .to = X×Y.π₂
    total-prod .π₂' .commute = I×J.π₂∘⟨⟩
```

The universal property follows from a bit of routine algebra involving
products.

```agda
    total-prod .has-is-total-product .⟨_,_⟩' f g .to = X×Y.⟨ f. to , g .to ⟩
    total-prod .has-is-total-product .⟨_,_⟩' f g .commute =
      I×J.unique₂
        (pulll I×J.π₁∘⟨⟩ ∙ f .commute)
        (pulll I×J.π₂∘⟨⟩ ∙ g .commute)
        (pulll I×J.π₁∘⟨⟩ ∙ pullr X×Y.π₁∘⟨⟩)
        (pulll I×J.π₂∘⟨⟩ ∙ pullr X×Y.π₂∘⟨⟩)
    total-prod .has-is-total-product .π₁∘⟨⟩' =
      Slice-pathp B _ X×Y.π₁∘⟨⟩
    total-prod .has-is-total-product .π₂∘⟨⟩' =
      Slice-pathp B _ X×Y.π₂∘⟨⟩
    total-prod .has-is-total-product .unique' p q =
      Slice-pathp B _ (X×Y.unique (λ i → p i .to) λ i → q i .to)
```
