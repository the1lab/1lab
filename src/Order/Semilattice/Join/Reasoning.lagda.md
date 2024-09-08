<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Delooping
open import Cat.Prelude

open import Order.Semilattice.Join
open import Order.Base

import Cat.Reasoning

import Order.Reasoning

open is-monoid
```
-->

```agda
module Order.Semilattice.Join.Reasoning
  {o ℓ} {P : Poset o ℓ} (slat : is-join-semilattice P)
  where
```

# Reasoning about join semilattices

This module proves some basic facts about [[join semilattices]], and
exposes reasoning combinators for working with them.

```agda
open is-join-semilattice slat public
open Order.Reasoning P public
```

The bottom element of a join semilattice is both a left and right
identity element with respect to joins.

```agda
∪-idl : ∀ {x} → bot ∪ x ≡ x
∪-idl = ≤-antisym (∪-universal _ ¡ ≤-refl) r≤∪

∪-idr : ∀ {x} → x ∪ bot ≡ x
∪-idr = ≤-antisym (∪-universal _ ≤-refl ¡) l≤∪
```

Therefore, every join semilattice is a monoid.

```agda
∪-is-monoid : is-monoid bot _∪_
∪-is-monoid .has-is-semigroup = ∪-is-semigroup
∪-is-monoid .idl = ∪-idl
∪-is-monoid .idr = ∪-idr

∪-monoid : Monoid-on ⌞ P ⌟
∪-monoid .Monoid-on.identity = bot
∪-monoid .Monoid-on._⋆_ = _∪_
∪-monoid .Monoid-on.has-is-monoid = ∪-is-monoid

module ∪ = Cat.Reasoning (B ∪-monoid) hiding (Ob)
```
