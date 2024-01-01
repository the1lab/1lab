<!--
```agda
open import Cat.Prelude

open import Order.Semilattice.Join
open import Order.Diagram.Join
open import Order.Subposet
open import Order.Base

import Order.Semilattice.Join.Reasoning
import Order.Reasoning
```
-->

```agda
module Order.Semilattice.Join.Subsemilattice where
```

# Subsets of Join Semilattices

```agda
module _ {o ℓ} {A : Poset o ℓ} (A-slat : is-join-semilattice A) where
  module A = Order.Semilattice.Join.Reasoning (A , A-slat)
  open is-join-semilattice
  open Join

  Subposet-is-join-semilattice
    : ∀ {ℓ'} {P : A.Ob → Prop ℓ'}
    → (∀ {x y} → x ∈ P → y ∈ P → (x A.∪ y) ∈ P)
    → A.bot ∈ P
    → is-join-semilattice (Subposet A P)
  Subposet-is-join-semilattice {P = P} ∪∈P bot∈P .has-joins (x , x∈P) (y , y∈P) =
    subposet-joins A.has-joins ∪∈P x∈P y∈P
  Subposet-is-join-semilattice {P = P} ∪∈P bot∈P .has-bottom =
    subposet-bottom A.has-bottom bot∈P
```
