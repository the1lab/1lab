```agda
open import Cat.Instances.Shape.Parallel
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Prelude

open import Data.Bool

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
`Limit`{.Agda} of a [parallel arrows] diagram.

[parallel arrows]: Cat.Instances.Shape.Parallel.html

```agda
is-equaliser→is-limit
  : ∀ {e a b} {f g : Hom a b} {equ : Hom e a}
  → (eq : is-equaliser C f g equ)
  → is-limit {C = C} (Fork f g) e (Fork→Cone (is-equaliser.equal eq))
is-equaliser→is-limit {e = e} {a} {b} {f} {g} {equ} is-eq =
  to-is-limitp ml λ where
    {true} → refl
    {false} → refl
  where
    module is-eq = is-equaliser is-eq
    open make-is-limit

    ml : make-is-limit (Fork f g) e
    ml .ψ true = f ∘ equ
    ml .ψ false = equ
    ml .commutes {true} {true} tt = idl _
    ml .commutes {false} {true} true = sym is-eq.equal
    ml .commutes {false} {true} false = refl
    ml .commutes {false} {false} tt = idl _
    ml .universal eta p =
      is-eq.universal (p {false} {true} false ∙ sym (p {false} {true} true))
    ml .factors {true} eta p =
      pullr is-eq.factors ∙ p {false} {true} false
    ml .factors {false} eta p =
      is-eq.factors
    ml .unique eta p other q =
      is-eq.unique (q false)

is-limit→is-equaliser
  : ∀ {a b} {f g : Hom a b} {K : Functor ⊤Cat C}
  → {eta : K F∘ !F => Fork f g}
  → is-ran !F (Fork f g) K eta
  → is-equaliser C f g (eta .η false)
is-limit→is-equaliser {a = a} {b} {f} {g} {K} {eta} lim = eq where
  module lim = is-limit lim

  parallel : ∀ {x} → Hom x a → (j : Bool) → Hom x (Fork {C = C} f g .F₀ j)
  parallel e′ true = f ∘ e′
  parallel e′ false = e′

  parallel-commutes
    : ∀ {x} {e′ : Hom x a}
    → f ∘ e′ ≡ g ∘ e′
    → ∀ i j → (h : Precategory.Hom ·⇉· i j)
    → Fork {C = C} f g .F₁ {i} {j} h ∘ parallel e′ i ≡ parallel e′ j
  parallel-commutes p true true tt = idl _
  parallel-commutes p false true true = sym p
  parallel-commutes p false true false = refl
  parallel-commutes p false false tt = idl _

  eq : is-equaliser C f g (eta .η false)
  eq .equal =
    sym (eta .is-natural false true false) ∙ eta .is-natural false true true
  eq .universal {e′ = e′} p =
    lim.universal (parallel e′) (λ {i} {j} h → parallel-commutes p i j h)
  eq .factors = lim.factors {j = false} _ _
  eq .unique {p = p} {other = other} q =
    lim.unique _ _ _ λ where
      true →
        ap (_∘ other) (intror (K .F-id) ∙ eta .is-natural false true true)
        ·· pullr q
        ·· sym p
      false → q

Equaliser→Limit : ∀ {a b} {f g : Hom a b} → Equaliser C f g → Limit (Fork {C = C} f g)
Equaliser→Limit eq = to-limit (is-equaliser→is-limit (has-is-eq eq))

Limit→Equaliser : ∀ {a b} {f g : Hom a b} → Limit (Fork {C = C} f g) → Equaliser C f g
Limit→Equaliser lim .apex = _
Limit→Equaliser lim .equ = _
Limit→Equaliser lim .has-is-eq =
  is-limit→is-equaliser (Limit.has-limit lim)
```
