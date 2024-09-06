<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Delooping
open import Cat.Prelude

open import Order.Semilattice.Meet
open import Order.Base

import Cat.Reasoning

import Order.Reasoning

open is-monoid
```
-->

```agda
module Order.Semilattice.Meet.Reasoning
  {o ℓ} {P : Poset o ℓ} (slat : is-meet-semilattice P)
  where
```

# Reasoning about meet semilattices

This module proves some basic facts about [[meet semilattices]], and
exposes reasoning combinators for working with them.

```agda
open Order.Reasoning P public
open is-meet-semilattice slat public
```

The top element of a meet semilattice is both a left and right
identity element with respect to meets.

```agda
∩-idl : ∀ {x} → top ∩ x ≡ x
∩-idl = ≤-antisym ∩≤r (∩-universal _ ! ≤-refl)

∩-idr : ∀ {x} → x ∩ top ≡ x
∩-idr = ≤-antisym ∩≤l (∩-universal _ ≤-refl !)
```

Therefore, every meet semilattice is a monoid.

```agda
∩-is-monoid : is-monoid top _∩_
∩-is-monoid .has-is-semigroup = ∩-is-semigroup
∩-is-monoid .idl = ∩-idl
∩-is-monoid .idr = ∩-idr

∩-monoid : Monoid-on ⌞ P ⌟
∩-monoid .Monoid-on.identity = top
∩-monoid .Monoid-on._⋆_ = _∩_
∩-monoid .Monoid-on.has-is-monoid = ∩-is-monoid

module ∩ = Cat.Reasoning (B ∩-monoid) hiding (Ob)
```
