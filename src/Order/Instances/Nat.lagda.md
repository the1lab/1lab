<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Nat.Order
open import Data.Nat.Base

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base
```
-->

```agda
module Order.Instances.Nat where
```

# The usual ordering on natural numbers

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
set of natural numbers.

```agda
Nat-poset : Poset lzero lzero
Nat-poset .P.Ob        = Nat
Nat-poset .P._≤_       = _≤_
Nat-poset .P.≤-thin    = ≤-is-prop
Nat-poset .P.≤-refl    = ≤-refl
Nat-poset .P.≤-trans   = ≤-trans
Nat-poset .P.≤-antisym = ≤-antisym

Nat-meets : ∀ x y → Meet Nat-poset x y
Nat-meets x y .glb                = min x y
Nat-meets x y .has-meet .meet≤l   = min-≤l x y
Nat-meets x y .has-meet .meet≤r   = min-≤r x y
Nat-meets x y .has-meet .greatest = min-is-glb x y

Nat-joins : ∀ x y → Join Nat-poset x y
Nat-joins x y .lub              = max x y
Nat-joins x y .has-join .least  = max-is-lub x y
Nat-joins x y .has-join .l≤join = max-≤l x y
Nat-joins x y .has-join .r≤join = max-≤r x y

Nat-bottom : Bottom Nat-poset
Nat-bottom .bot          = 0
Nat-bottom .has-bottom x = 0≤x

Nat-no-top : ¬ Top Nat-poset
Nat-no-top record { top = greatest ; has-top = is-greatest } =
  let
    rem₁ : suc greatest ≤ greatest
    rem₁ = is-greatest (suc greatest)
  in ¬sucx≤x _ rem₁
```
