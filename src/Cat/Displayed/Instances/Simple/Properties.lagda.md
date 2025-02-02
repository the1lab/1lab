---
description: |
  Properties of simple fibrations.
---
<!--
```agda
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Diagram.Product
open import Cat.Displayed.Base

open import Cat.Prelude

import Cat.Displayed.Instances.Simple
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Instances.Simple.Properties
  {o ℓ} (B : Precategory o ℓ)
  (has-prods : ∀ X Y → Product B X Y)
  where
```

<!--
```agda
open Cat.Reasoning B
open Cat.Displayed.Instances.Simple B has-prods
  renaming (Simple to Simple[B])
open Binary-products B has-prods
```
-->

# Properties of simple fibrations

This module collects some useful properties of [[simple fibrations]].

## Total products in simple fibrations

Every simple fibration has all [[total products]].

```agda
simple-total-product
  : ∀ {Γ Δ A B : Ob}
  → Total-product Simple[B] (has-prods Γ Δ) A B
```

```agda
simple-total-product {Γ} {Δ} {A} {B} = total-prod where
  open is-total-product
  open Total-product

  total-prod : Total-product Simple[B] (has-prods Γ Δ) A B
```

The apex of the total product is simply given by a product in $\cB$.
We can obtain the projections $(\Gamma \times \Delta) \times (A \times B) \to A$
and $(\Gamma \times \Delta) \times (A \times B) \to B$ by composing projections.

```agda
  total-prod .apex' = A ⊗₀ B
  total-prod .π₁' = π₁ ∘ π₂
  total-prod .π₂' = π₂ ∘ π₂
```

The universal property follows from some straightforward algebra.

```agda
  total-prod .has-is-total-product .⟨_,_⟩' f g = ⟨ f , g ⟩
  total-prod .has-is-total-product .π₁∘⟨⟩' =
    pullr π₂∘⟨⟩ ∙ π₁∘⟨⟩
  total-prod .has-is-total-product .π₂∘⟨⟩' =
    pullr π₂∘⟨⟩ ∙ π₂∘⟨⟩
  total-prod .has-is-total-product .unique' p q =
    ⟨⟩-unique (pushr (sym π₂∘⟨⟩) ∙ p) (pushr (sym π₂∘⟨⟩) ∙ q)
```
