<!--
```agda
open import Algebra.Monoid

open import Cat.Instances.Delooping
open import Cat.Prelude

open import Order.Semilattice.Join
open import Order.Base

import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Order.Semilattice.Join.Reasoning {o ℓ} (L : Join-semilattice o ℓ) where
```

```agda
open is-join-semilattice (L .snd) public
open Order.Reasoning (L .fst) public

po : Poset o ℓ
po = L .fst

∪-idl : ∀ {x} → bot ∪ x ≡ x
∪-idl = ≤-antisym (∪-universal _ ¡ ≤-refl) r≤∪

∪-idr : ∀ {x} → x ∪ bot ≡ x
∪-idr = ≤-antisym (∪-universal _ ≤-refl ¡) l≤∪

∪-is-monoid : is-monoid bot _∪_
∪-is-monoid .has-is-semigroup = ∪-is-semigroup
∪-is-monoid .idl = ∪-idl
∪-is-monoid .idr = ∪-idr

∪-monoid : Monoid-on ⌞ L ⌟
∪-monoid .Monoid-on.identity = bot
∪-monoid .Monoid-on._⋆_ = _∪_
∪-monoid .Monoid-on.has-is-monoid = ∪-is-monoid

module ∪ = Cat.Reasoning (B ∪-monoid) hiding (Ob)
```
