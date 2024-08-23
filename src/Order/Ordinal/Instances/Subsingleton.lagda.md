---
description: |
  Subsingleton ordinals.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Base

open import Order.Ordinal
```
-->
```agda
module Order.Ordinal.Instances.Subsingleton where
```

```agda
Subsingletonₒ : (P : Ω) → Ordinal lzero lzero
Subsingletonₒ P .Ordinal.Ob = ∣ P ∣
Subsingletonₒ P .Ordinal._≺_ _ _ = ⊥
Subsingletonₒ P .Ordinal.≺-wf x = acc (λ _ ff → absurd ff)
Subsingletonₒ P .Ordinal.≺-ext _ _ = prop!
Subsingletonₒ P .Ordinal.≺-trans ff _ = ff
Subsingletonₒ P .Ordinal.≺-is-prop = hlevel 1
```
