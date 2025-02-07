<!--
```agda
open import Cat.Instances.Shape.Parallel
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Functor.Kan.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Limit.Equaliser {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C

open is-equaliser
open Equaliser
open Functor
open _=>_
```
-->

We establish the correspondence between `Equaliser`{.Agda} and the
`Limit`{.Agda} of a [[parallel arrows]] diagram.

```agda
is-equaliser→is-limit
  : ∀ {e} (F : Functor ·⇉· C) {equ : Hom e (F .F₀ false)}
  → (eq : is-equaliser C (forkl F) (forkr F) equ)
  → is-limit {C = C} F e (Fork→Cone F (is-equaliser.equal eq))
is-equaliser→is-limit {e} F {equ} is-eq =
  to-is-limitp ml λ where
    {true} → refl
    {false} → refl
  where
    module is-eq = is-equaliser is-eq
    open make-is-limit

    ml : make-is-limit F e
    ml .ψ true = forkl F ∘ equ
    ml .ψ false = equ
    ml .commutes {true} {true} tt = eliml (F .F-id)
    ml .commutes {false} {true} true = sym is-eq.equal
    ml .commutes {false} {true} false = refl
    ml .commutes {false} {false} tt = eliml (F .F-id)
    ml .universal eps p =
      is-eq.universal (p {false} {true} false ∙ sym (p {false} {true} true))
    ml .factors {true} eps p =
      pullr is-eq.factors ∙ p {false} {true} false
    ml .factors {false} eps p =
      is-eq.factors
    ml .unique eps p other q =
      is-eq.unique (q false)

is-limit→is-equaliser
  : ∀ (F : Functor ·⇉· C) {K : Functor ⊤Cat C}
  → {eps : K F∘ !F => F}
  → is-ran !F F K eps
  → is-equaliser C (forkl F) (forkr F) (eps .η false)
is-limit→is-equaliser F {K} {eps} lim = eq where
  module lim = is-limit lim

  parallel
    : ∀ {x} → Hom x (F .F₀ false)
    → (j : Bool) → Hom x (F .F₀ j)
  parallel e' true = forkl F ∘ e'
  parallel e' false = e'

  parallel-commutes
    : ∀ {x} {e' : Hom x (F .F₀ false)}
    → forkl F ∘ e' ≡ forkr F ∘ e'
    → ∀ i j → (h : ·⇉· .Precategory.Hom i j)
    → F .F₁ {i} {j} h ∘ parallel e' i ≡ parallel e' j
  parallel-commutes p true true tt = eliml (F .F-id)
  parallel-commutes p false true true = sym p
  parallel-commutes p false true false = refl
  parallel-commutes p false false tt = eliml (F .F-id)

  eq : is-equaliser C (forkl F) (forkr F) (eps .η false)
  eq .equal =
    sym (eps .is-natural false true false) ∙ eps .is-natural false true true
  eq .universal {e' = e'} p =
    lim.universal (parallel e') (λ {i} {j} h → parallel-commutes p i j h)
  eq .factors = lim.factors {j = false} _ _
  eq .unique {p = p} {other = other} q =
    lim.unique _ _ _ λ where
      true →
        ap (_∘ other) (intror (K .F-id) ∙ eps .is-natural false true true)
        ·· pullr q
        ·· sym p
      false → q

Equaliser→Limit : ∀ {F : Functor ·⇉· C} → Equaliser C (forkl F) (forkr F) → Limit F
Equaliser→Limit {F = F} eq = to-limit (is-equaliser→is-limit F (has-is-eq eq))

Limit→Equaliser : ∀ {a b} {f g : Hom a b} → Limit {C = C} (Fork f g) → Equaliser C f g
Limit→Equaliser lim .apex = _
Limit→Equaliser lim .equ = _
Limit→Equaliser {f = f} {g} lim .has-is-eq =
  is-limit→is-equaliser (Fork f g) (Limit.has-limit lim)
```
