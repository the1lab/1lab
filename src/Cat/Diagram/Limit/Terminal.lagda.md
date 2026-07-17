---
description: |
  A correspondence is established between terminal objects
  and limits of empty diagrams.
---

<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Shape.Initial
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Limit.Terminal {o h} (C : Precategory o h) where
```

<!--
```agda
open Precategory C

open Terminal
open Functor
open _=>_
```
-->

# Terminal objects are limits

A [[terminal object]] is equivalently defined as a limit of the empty diagram.

```agda
is-limit→is-terminal
  : ∀ {T : Ob} {eps : Const T => ¡F}
  → is-limit {C = C} ¡F T eps
  → is-terminal C T
is-limit→is-terminal lim Y = record where
  module lim = is-limit lim

  centre  = lim.universal (λ ()) (λ ())
  paths _ = lim.unique _ _ _ λ ()

is-terminal→is-limit : ∀ {T : Ob} {F : Functor ⊥Cat C} → is-terminal C T → is-limit {C = C} F T ¡nt
is-terminal→is-limit {T} {F} term = to-is-limitp ml λ {} where
  open make-is-limit
  ml : make-is-limit F T
  ml .ψ ()
  ml .commutes ()
  ml .universal _ _ = term _ .centre
  ml .factors {}
  ml .unique _ _ _ _ = term _ .paths _

Limit→Terminal : Limit {C = C} ¡F → Terminal C
Limit→Terminal lim .top = Limit.apex lim
Limit→Terminal lim .has⊤ = is-limit→is-terminal (Limit.has-limit lim)

Terminal→Limit : ∀ {F : Functor ⊥Cat C} → Terminal C → Limit {C = C} F
Terminal→Limit term = to-limit (is-terminal→is-limit (term .has⊤))
```
