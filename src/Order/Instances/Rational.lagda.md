<!--
```agda
open import 1Lab.Prelude

open import Data.Rational.Order
open import Data.Rational.Base

open import Order.Total
open import Order.Base
```
-->

```agda
module Order.Instances.Rational where
```

<!--
```agda
private module P = Poset
```
-->

# The usual ordering on the rationals

```agda
Ratio-poset : Poset lzero lzero
Ratio-poset .P.Ob        = Ratio
Ratio-poset .P._≤_       = _≤_
Ratio-poset .P.≤-thin    = hlevel 1
Ratio-poset .P.≤-refl    = ≤-refl
Ratio-poset .P.≤-trans   = ≤-trans
Ratio-poset .P.≤-antisym = ≤-antisym

Ratio-is-dec-total : is-decidable-total-order Ratio-poset
Ratio-is-dec-total = from-weakly-total (≤-is-weakly-total _ _)
```
