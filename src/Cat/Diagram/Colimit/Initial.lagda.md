---
description: |
  A correspondence is established between initial objects
  and colimits of empty diagrams.
---

<!--
```agda
open import Cat.Instances.Shape.Initial
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Constant
open import Cat.Diagram.Initial
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Colimit.Initial {o h} (C : Precategory o h) where
```

<!--
```agda
open Precategory C

open Initial
open Functor
open _=>_
```
-->

# Initial objects are colimits

An [[initial object]] is equivalently defined as a colimit of the empty diagram.

```agda
is-colimit→is-initial
  : ∀ {T : Ob} {eta : ¡F => Const T}
  → is-colimit {C = C} ¡F T eta
  → is-initial C T
is-colimit→is-initial colim Y = record where
  module colim = is-colimit colim

  centre  = colim.universal (λ ()) λ ()
  paths _ = colim.unique _ _ _ λ ()

is-initial→is-colimit : ∀ {T : Ob} {F : Functor ⊥Cat C} → is-initial C T → is-colimit {C = C} F T ¡nt
is-initial→is-colimit {T} {F} init = to-is-colimitp mc λ {} where
  open make-is-colimit
  mc : make-is-colimit F T
  mc .ψ ()
  mc .commutes ()
  mc .universal _ _ = init _ .centre
  mc .factors {}
  mc .unique _ _ _ _ = init _ .paths _

Colimit→Initial : Colimit {C = C} ¡F → Initial C
Colimit→Initial colim .bot = Colimit.coapex colim
Colimit→Initial colim .has⊥ = is-colimit→is-initial (Colimit.has-colimit colim)

Initial→Colimit : ∀ {F : Functor ⊥Cat C} → Initial C → Colimit {C = C} F
Initial→Colimit init = to-colimit (is-initial→is-colimit (init .has⊥))
```
