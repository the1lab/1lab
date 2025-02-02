---
description: |
  Properties of family fibrations.
---
<!--
```agda
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Displayed.Instances.Family
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Product
open import Cat.Displayed.Base

open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Family.Properties where
```

# Properties of family fibrations

This module proves a collection of useful properties about the [[family fibration]].

# Total products

<!--
```agda
module _ {o ℓ κ} (C : Precategory o ℓ) where
  private
    module C = Cat.Reasoning C
    module Fam[C] = Displayed (Family C {κ})
```
-->

A [[total product]] in the family fibration of $\cC$ corresponds to a family
of [[products]] in $\cC$.

```agda
  fam-total-product
    : ∀ {I J : Set κ} {Xᵢ : ⌞ I ⌟ → C.Ob} {Yⱼ : ⌞ J ⌟ → C.Ob}
    → (∀ i j → Product C (Xᵢ i) (Yⱼ j))
    → Total-product (Family C) (Sets-products I J) Xᵢ Yⱼ
```

All of the relevant morphisms come directly from products in $\cC$.

```agda
  fam-total-product {I = I} {J = J} {Xᵢ = Xᵢ} {Yⱼ = Yⱼ} C-prods = total-prod where
    open is-total-product
    open Total-product

    module _ i j where
      open Product (C-prods i j) renaming (apex to Xᵢ×Yⱼ) using () public

    module _ {i j} where
      open Product (C-prods i j) hiding (apex) public

    total-prod : Total-product (Family C) (Sets-products I J) Xᵢ Yⱼ
    total-prod .apex' (i , j) = Xᵢ×Yⱼ i j
    total-prod .π₁' (i , j) = π₁
    total-prod .π₂' (i , j) = π₂
    total-prod .has-is-total-product .⟨_,_⟩' fₖ gₖ k = ⟨ fₖ k , gₖ k ⟩
```

The $\beta$ laws are easy applications of function extensionality, but
the $\eta$ law requires a bit of cubical-fu to get the types to line
up.

```agda
    total-prod .has-is-total-product .π₁∘⟨⟩' = ext (λ k → π₁∘⟨⟩)
    total-prod .has-is-total-product .π₂∘⟨⟩' = ext (λ k → π₂∘⟨⟩)
    total-prod .has-is-total-product .unique' {a' = Zₖ} {p1 = p1} {p2 = p2} {other' = other'} p q i k =
      unique
        (coe0→i (λ i → π₁ C.∘ other-line k i ≡ p i k) i refl)
        (coe0→i (λ i → π₂ C.∘ other-line k i ≡ q i k) i refl)
        i
      where
        other-line : ∀ k i → C.Hom (Zₖ k) (Xᵢ×Yⱼ (p1 i k) (p2 i k))
        other-line k i = coe0→i (λ i → C.Hom (Zₖ k) (Xᵢ×Yⱼ (p1 i k) (p2 i k))) i (other' k)
```
