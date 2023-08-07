<!--
```agda
open import Cat.Prelude

open import Order.Base
open import Order.DCPO

import Order.Reasoning
import Order.Diagram.Lub
import Order.Diagram.Fixpoint as Fixpoint
```
-->

```agda
module Order.DCPO.Reasoning {o ℓ} (P : DCPO o ℓ) where
```

<!--
```agda
-- We re-export a bunch of definitions involving posets, and tweak
-- those that use poset morphisms instead of scott-continuous functions.
open DCPO-on (P .snd) public using
  (poset-on; poset; has-dcpo; directed-lubs; module ⋃; ⋃)
open Order.Reasoning (DCPO-on.poset (P .snd)) public
open Order.Diagram.Lub (DCPO-on.poset (P .snd)) public

dcpo-on : DCPO-on ℓ Ob
dcpo-on = P .snd

is-least-fixpoint : (f : DCPOs.Hom P P) → Ob → Type _
is-least-fixpoint f = Fixpoint.is-least-fixpoint poset (Scott→Mono f)

Least-fixpoint : (f : DCPOs.Hom P P) → Type _
Least-fixpoint f = Fixpoint.Least-fixpoint poset (Scott→Mono f)

open Fixpoint.is-least-fixpoint public
open Fixpoint.Least-fixpoint public
```
-->

# Reasoning for DCPOs

This module re-exports definitions and reasoning syntax for the
underlying poset of a DCPO, and also proves some simple helper lemmas
about DCPOs.

```agda
⋃-pointwise
  : ∀ {Ix} {s s' : Ix → Ob}
  → {fam : is-directed-family poset s} {fam' : is-directed-family poset s'}
  → (∀ ix → s ix ≤ s' ix)
  → ⋃ s fam ≤ ⋃ s' fam'
⋃-pointwise p = ⋃.least _ _ (⋃ _ _) λ ix →
  ≤-trans (p ix) (⋃.fam≤lub _ _ ix)
```
