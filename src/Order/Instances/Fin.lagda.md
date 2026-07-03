<!--
```agda
open import 1Lab.Prelude

open import Data.Fin.Base

open import Order.Base

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Order.Instances.Fin where
```

<!--
```agda
private module P = Poset
```
-->

# The poset of finite ordinals {defines="finite-ordinal-poset"}

The [[finite set|finite sets]] $[n] = \{0, \dots, n - 1\}$ inherits a
[[partial order]] from the natural numbers, making it a finite linear
order: the $n$-th finite *ordinal*. These posets are the objects of the
[[simplex category]], and their induced categories are the shapes of
composition in a [[simplicial set|simplicial-set]].

```agda
Fin-poset : Nat → Poset lzero lzero
Fin-poset n .P.Ob        = Fin n
Fin-poset n .P._≤_       = _≤_
Fin-poset n .P.≤-thin    = Nat.≤-is-prop
Fin-poset n .P.≤-refl    = Nat.≤-refl
Fin-poset n .P.≤-trans   = Nat.≤-trans
Fin-poset n .P.≤-antisym p q = fin-ap (Nat.≤-antisym p q)
```
