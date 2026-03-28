---
description: |
  Upper sets.
---

<!--
```agda
open import Cat.Prelude

open import Order.Instances.Pointwise
open import Order.Instances.Props
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Instances.Upper where
```

# Upper sets

:::{.definition #upper-set}
An **upper set** of a [[poset]] $P$ is a subset $F \subseteq P$ such that:

$$
\forall (x y : P).\ x \leq y \to x \in F \to y \in F
$$

Equivalently, an upper set $F \subseteq P$ is a monotone map $F : P \to \Omega$ to
the poset of propositions.
:::


```agda
Upper-sets : ∀ {o ℓ} → Poset o ℓ → Poset (o ⊔ ℓ) o
Upper-sets P = Poset[ P , Props ]

Upper-set : ∀ {o ℓ} (P : Poset o ℓ) → Type _
Upper-set P =  ⌞ Upper-sets P ⌟
```

Upper sets are the order-theoretic analog to [[functors]] $\cC \to \Sets$, and
thus come with their own version of the [[covariant yoneda embedding]] which
sends an element $x : P$ to the upper set $\left\{ a : P \mid x \leq a \right\}$.

```agda
module _ {o ℓ} (P : Poset o ℓ) where
  private module P = Order.Reasoning P

  ↑ : ⌞ P ⌟ → Upper-set P
  ↑ x .hom a = elΩ (x P.≤ a)
  ↑ x .pres-≤ a≤b x≤a = ⦇ P.≤-trans x≤a (pure a≤b) ⦈

  よcovₚ : Monotone (P ^opp) (Upper-sets P)
  よcovₚ .hom = ↑
  よcovₚ .pres-≤ y≤x a x≤a = ⦇ P.≤-trans (pure y≤x) x≤a ⦈
```

## Duality

Upper sets are dual to [[lower sets]]; see that page for a proof.
