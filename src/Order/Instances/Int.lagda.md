<!--
```agda
open import 1Lab.Prelude

open import Data.Int.Order
open import Data.Int

open import Order.Diagram.Glb
open import Order.Diagram.Lub
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

```agda
Int-poset : Poset lzero lzero
Int-poset .P.Ob     = Int
Int-poset .P._≤_    = _≤_
Int-poset .P.≤-thin = hlevel!
Int-poset .P.≤-refl    {x}         = ≤-refl {x}
Int-poset .P.≤-trans   {x} {y} {z} = ≤-trans {x} {y} {z}
Int-poset .P.≤-antisym {x} {y}     = ≤-antisym {x} {y}
```
