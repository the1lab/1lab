---
description: |
  The covariant poset of elements.
---

<!--
```agda
open import Cat.Prelude

open import Order.Instances.Props
open import Order.Base
```
-->

```agda
module Order.Instances.Elements.Covariant where
```

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
```
-->

# The covariant poset of elements

:::{.definition #covariant-poset-of-elements}
The **covariant poset of elements** of an [[upper set]] $F : P \to \Omega$, denoted
$\int F$, is the poset whose elements are the $x : P$ such that $F(x)$ holds, where the order
is given by the ordering of $P$.
:::


```agda
  ∫ : (F : Monotone P Props) → Poset o ℓ
  ∫ F .Poset.Ob = ∫ₚ F
  ∫ F .Poset._≤_ (x , _) (y , _) = x ≤ y
  ∫ F .Poset.≤-thin = hlevel 1
  ∫ F .Poset.≤-refl = ≤-refl
  ∫ F .Poset.≤-trans = ≤-trans
  ∫ F .Poset.≤-antisym x≤y y≤x = Σ-prop-path! (≤-antisym x≤y y≤x)
```

As the name suggests, this is the order-theoretic analog of the [[covariant category of elements]].
