<!--
```agda
open import 1Lab.Prelude

open import Data.Int.Order
open import Data.Int

open import Order.Diagram.Glb
open import Order.Diagram.Lub
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
Int-poset .P.Ob     = Int
Int-poset .P._≤_    = _≤_
Int-poset .P.≤-thin = hlevel!
Int-poset .P.≤-refl    {x}         = ≤-refl {x}
Int-poset .P.≤-trans   {x} {y} {z} = ≤-trans {x} {y} {z}
Int-poset .P.≤-antisym {x} {y}     = ≤-antisym {x} {y}
```

It's worth pointing out that the ordering on integers is a [[decidable
total order]], essentially because the ordering on naturals also is.
This lets us get the operations `minℤ`{.Agda} and `maxℤ`{.Agda} "for
free", and they compute on points as expected:

```agda
Int-is-dec-total : is-decidable-total-order Int-poset
Int-is-dec-total = from-weakly-total (≤-is-weakly-total _ _)

open minmax (Int-is-dec-total .is-decidable-total-order.has-is-total)
```

<!--
```agda
  renaming
    ( min      to minℤ
    ; min-≤l   to minℤ-≤l
    ; min-≤r   to minℤ-≤r
    ; min-univ to minℤ-is-meet

    ; max      to maxℤ
    ; max-≤l   to maxℤ-≤l
    ; max-≤r   to maxℤ-≤r
    ; max-univ to maxℤ-is-join)
  using () public
```
-->

```agda
_ : maxℤ 10 -10 ≡ 10
_ = refl

_ : minℤ 10 -10 ≡ -10
_ = refl
```
