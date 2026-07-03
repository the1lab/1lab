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

open Functor
open _=>_
```
-->

# Terminal objects are limits

A [[terminal object]] is equivalently defined as a limit of the empty diagram.

```agda

module _ (Dia : Functor ⊥Cat C) where

  is-limit→is-terminal
    : ∀ {T : Ob} {eps : Const T => Dia}
    → is-limit {C = C} Dia T eps
    → is-terminal C T
  {-# INLINE is-limit→is-terminal #-}
  is-limit→is-terminal lim = record
    { ! = lim.universal (λ ()) (λ ())
    ; !-unique = λ h → lim.unique (λ ()) (λ ()) h (λ ())
    }
    where module lim = is-limit lim

  is-terminal→is-limit : ∀ {T : Ob} {F : Functor ⊥Cat C} → is-terminal C T → is-limit {C = C} F T ¡nt
  is-terminal→is-limit {T} {F} term = to-is-limitp ml λ {} where
    open is-terminal term
    open make-is-limit

    ml : make-is-limit F T
    ml .ψ ()
    ml .commutes ()
    ml .universal _ _ = !
    ml .factors {}
    ml .unique _ _ _ _ = !-unique _

  Limit→Terminal
    : Limit Dia → Terminal C
  {-# INLINE Limit→Terminal #-}
  Limit→Terminal lim = record
    { top = Limit.apex lim
    ; has-is-term = is-limit→is-terminal (Limit.has-limit lim)
    }

  Terminal→Limit : Terminal C → Limit Dia
  Terminal→Limit term = to-limit (is-terminal→is-limit (Terminal.has-is-term term))
```
