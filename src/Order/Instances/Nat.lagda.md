<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Nat.Order
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Sum.Base

open import Order.Semilattice.Join
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Directed
open import Order.Total
open import Order.Base
```
-->

```agda
module Order.Instances.Nat where
```

# The usual ordering on natural numbers {defines="poset-of-natural-numbers"}

<!--
```agda
private module P = Poset
open is-meet
open is-join
open Bottom
open Meet
open Join
```
-->

This module deals with noting down facts about the usual ordering on the
set of natural numbers; most of the proofs are in the modules
[`Data.Nat.Properties`](Data.Nat.Properties.html) and
[`Data.Nat.Order`](Data.Nat.Order.html).

We have already shown that the usual ordering (or "numeric") ordering on
the natural numbers is a poset:

```agda
Nat-poset : Poset lzero lzero
Nat-poset .P.Ob        = Nat
Nat-poset .P._≤_       = _≤_
Nat-poset .P.≤-thin    = ≤-is-prop
Nat-poset .P.≤-refl    = ≤-refl
Nat-poset .P.≤-trans   = ≤-trans
Nat-poset .P.≤-antisym = ≤-antisym
```

We've also defined procedures for computing the [[meets]] and [[joins]]
of pairs of natural numbers:

```agda
Nat-min-is-meet : ∀ x y → is-meet Nat-poset x y (min x y)
Nat-min-is-meet x y .meet≤l = min-≤l x y
Nat-min-is-meet x y .meet≤r = min-≤r x y
Nat-min-is-meet x y .greatest = min-univ x y

Nat-max-is-join : ∀ x y → is-join Nat-poset x y (max x y)
Nat-max-is-join x y .l≤join = max-≤l x y
Nat-max-is-join x y .r≤join = max-≤r x y
Nat-max-is-join x y .least  = max-univ x y
```

<!--
```agda
Nat-meets : ∀ x y → Meet Nat-poset x y
Nat-meets x y .glb = min x y
Nat-meets x y .has-meet = Nat-min-is-meet x y

Nat-joins : ∀ x y → Join Nat-poset x y
Nat-joins x y .lub = max x y
Nat-joins x y .has-join = Nat-max-is-join x y
```
-->

It's straightforward to show that this order is _bounded below_, since
we have $0 \le x$ for any $x$.

```agda
Nat-bottom : Bottom Nat-poset
Nat-bottom .bot          = 0
Nat-bottom .has-bottom x = 0≤x
```

This means that the ordering forms a [[join semilattice]].

```agda
Nat-is-join-semilattice : is-join-semilattice Nat-poset
Nat-is-join-semilattice .is-join-semilattice._∪_ = max
Nat-is-join-semilattice .is-join-semilattice.∪-joins = Nat-max-is-join
Nat-is-join-semilattice .is-join-semilattice.has-bottom = Nat-bottom
```

<!--
```agda
Nat-is-upwards-directed : is-upwards-directed Nat-poset
Nat-is-upwards-directed = is-join-slat→is-upwards-directed Nat-is-join-semilattice
```
-->

However, it's _not_ bounded above:

```agda
Nat-no-top : ¬ Top Nat-poset
Nat-no-top record { top = greatest ; has-top = is-greatest } =
  let
    rem₁ : suc greatest ≤ greatest
    rem₁ = is-greatest (suc greatest)
  in ¬sucx≤x _ rem₁
```

This is also a [[decidable total order]]; we show totality by proving
weak totality, since we already know that the ordering is decidable.

```agda
Nat-is-dec-total : is-decidable-total-order Nat-poset
Nat-is-dec-total = from-weakly-total (≤-is-weakly-total _ _)
```
