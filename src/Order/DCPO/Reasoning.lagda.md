<!--
```agda
open import Cat.Prelude

open import Order.Base
open import Order.DCPO

import Order.Diagram.Lub
import Order.Reasoning
```
-->

```agda
module Order.DCPO.Reasoning {o ℓ} (P : DCPO o ℓ) where
```

# Reasoning with DCPOs

This module re-exports definitions and reasoning syntax for the
underlying poset of a DCPO, and also proves some simple helper lemmas.

```agda
poset : Poset o ℓ
poset = P .fst

open Order.Reasoning poset public

poset-on : Poset-on ℓ Ob
poset-on = P .fst .snd

has-dcpo : is-dcpo poset
has-dcpo = P .snd

open is-dcpo has-dcpo public
```

<!--
```agda
open Order.Diagram.Lub poset public
```
-->

```agda
⋃-pointwise
  : ∀ {Ix} {s s' : Ix → Ob}
  → {fam : is-directed-family poset s} {fam' : is-directed-family poset s'}
  → (∀ ix → s ix ≤ s' ix)
  → ⋃ s fam ≤ ⋃ s' fam'
⋃-pointwise p = ⋃.least _ _ (⋃ _ _) λ ix →
  ≤-trans (p ix) (⋃.fam≤lub _ _ ix)
```
