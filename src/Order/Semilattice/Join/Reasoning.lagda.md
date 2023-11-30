<!--
```agda
open import Algebra.Monoid

open import Data.Fin.Base using (Fin; fzero; fsuc)

open import Cat.Instances.Delooping
open import Cat.Prelude

open import Order.Semilattice.Join
open import Order.Diagram.Lub
open import Order.Base

import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Order.Semilattice.Join.Reasoning where
```

```agda
module Join-semilattice {o ℓ} (L : Join-semilattice o ℓ) where
  open Order.Reasoning (L .fst) public
  open is-join-semilattice (L .snd) public

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

  open Cat.Reasoning (B ∪-monoid) public
```
