<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Join
open import Order.Lattice
open import Order.Base

import Order.Semilattice.Join.Reasoning
import Order.Semilattice.Meet.Reasoning
import Order.Reasoning as Pos
```
-->

```agda
module Order.Lattice.Reasoning {o ℓ} {P : Poset o ℓ} (lat : is-lattice P) where
```

<!--
```agda
open is-lattice lat public
open Pos P
```
-->

# Reasoning in lattices

This module provides some basic reasoning combinators for [[lattices]].

<!--
```agda
open Order.Semilattice.Meet.Reasoning has-meet-slat using (∩-idl; ∩-idr; module ∩) public
open Order.Semilattice.Join.Reasoning has-join-slat using (∪-idl; ∪-idr; module ∪) public
```
-->

First, we show that we have half of a distributive law that states that
meets distribute over joins. For the converse to hold, $P$ must be a
[[distributive lattice]].

```agda
abstract
  ∪-∩-distribl-≤ : ∀ {x y z} → (x ∩ y) ∪ (x ∩ z) ≤ x ∩ (y ∪ z)
  ∪-∩-distribl-≤ = ∪-universal _
    (∩-universal _ ∩≤l (≤-trans ∩≤r l≤∪))
    (∩-universal _ ∩≤l (≤-trans ∩≤r r≤∪))
```

We can prove a dual result for joins distributing over meets.

```agda
  ∩-∪-distribl-≤ : ∀ {x y z} → x ∪ (y ∩ z) ≤ (x ∪ y) ∩ (x ∪ z)
  ∩-∪-distribl-≤ = ∪-universal _
    (∩-universal _ l≤∪ l≤∪)
    (∩-universal _ (≤-trans ∩≤l r≤∪) (≤-trans ∩≤r r≤∪))
```

<!--
```agda
  ∪-∩-distribr-≤ : ∀ {x y z} → (x ∩ z) ∪ (y ∩ z) ≤ (x ∪ y) ∩ z
  ∪-∩-distribr-≤ = ∪-universal _
    (∩-universal _ (≤-trans ∩≤l l≤∪) ∩≤r)
    (∩-universal _ (≤-trans ∩≤l r≤∪) ∩≤r)

  ∩-∪-distribr-≤ : ∀ {x y z} → (x ∩ y) ∪ z ≤ (x ∪ z) ∩ (y ∪ z)
  ∩-∪-distribr-≤ = ∪-universal _
    (∩-universal _ (≤-trans ∩≤l l≤∪) (≤-trans ∩≤r l≤∪))
    (∩-universal _ r≤∪ r≤∪)
```
-->

We also have *absorptive* laws for meets over joins (and joins over
meets).

```agda
  ∩-absorbr : ∀ {x y} → (x ∪ y) ∩ x ≡ x
  ∩-absorbr = ≤-antisym ∩≤r (∩-universal _ l≤∪ ≤-refl)

  ∩-absorbl : ∀ {x y} → x ∩ (x ∪ y) ≡ x
  ∩-absorbl = ∩-comm ∙ ∩-absorbr

  ∪-absorbr : ∀ {x y} → (x ∩ y) ∪ x ≡ x
  ∪-absorbr = ≤-antisym (∪-universal _ ∩≤l ≤-refl) r≤∪

  ∪-absorbl : ∀ {x y} → x ∪ (x ∩ y) ≡ x
  ∪-absorbl = ∪-comm ∙ ∪-absorbr
```
