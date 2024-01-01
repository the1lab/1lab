<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Delooping
open import Cat.Prelude

open import Order.Semilattice.Meet
open import Order.Base

import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Order.Semilattice.Meet.Reasoning {o ℓ} (L : Meet-semilattice o ℓ) where
```

```agda
open Order.Reasoning (L .fst) public
open is-meet-semilattice (L .snd) public

po : Poset o ℓ
po = L .fst

∩-idl : ∀ {x} → top ∩ x ≡ x
∩-idl = ≤-antisym ∩≤r (∩-universal _ ! ≤-refl)

∩-idr : ∀ {x} → x ∩ top ≡ x
∩-idr = ≤-antisym ∩≤l (∩-universal _ ≤-refl !)

∩-is-monoid : is-monoid top _∩_
∩-is-monoid .has-is-semigroup = ∩-is-semigroup
∩-is-monoid .idl = ∩-idl
∩-is-monoid .idr = ∩-idr

∩-monoid : Monoid-on ⌞ L ⌟
∩-monoid .Monoid-on.identity = top
∩-monoid .Monoid-on._⋆_ = _∩_
∩-monoid .Monoid-on.has-is-monoid = ∩-is-monoid

module ∩ = Cat.Reasoning (B ∩-monoid) hiding (Ob)
```
