<!--
```agda
open import 1Lab.Prelude

open import Data.Int.Order
open import Data.Int

open import Order.Total
open import Order.Base
```
-->

```agda
module Order.Instances.Int where
```

<!--
```agda
private module P = Poset
```
-->

# The usual ordering on the integers

This module deals with noting down facts about the usual ordering on the
set of integers. Most of the proofs are in the module
[`Data.Int.Order`](Data.Int.Order.html).

```agda
Int-poset : Poset lzero lzero
Int-poset .P.Ob        = Int
Int-poset .P._≤_       = _≤_
Int-poset .P.≤-thin    = hlevel 1
Int-poset .P.≤-refl    = ≤-refl
Int-poset .P.≤-trans   = ≤-trans
Int-poset .P.≤-antisym = ≤-antisym
```

It's worth pointing out that the ordering on integers is a [[decidable
total order]], essentially because the ordering on naturals also is.

```agda
Int-is-dec-total : is-decidable-total-order Int-poset
Int-is-dec-total = from-weakly-total (≤-is-weakly-total _ _)
```
