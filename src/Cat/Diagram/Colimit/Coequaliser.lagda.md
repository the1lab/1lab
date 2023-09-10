<!--
```agda
open import Cat.Instances.Shape.Parallel
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Kan.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Colimit.Coequaliser {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C

open is-coequaliser
open Coequaliser
open Functor
open _=>_
```
-->

We establish the correspondence between `Coequaliser`{.Agda} and the
`Colimit`{.Agda} of a [[parallel arrows]] diagram.

```agda
is-coequaliser→is-colimit
  : ∀ {e} (F : Functor ·⇉· C) {coequ : Hom (F .F₀ true) e}
  → (coeq : is-coequaliser C (forkl F) (forkr F) coequ)
  → is-colimit {C = C} F e (Cofork→Cocone F (is-coequaliser.coequal coeq))
is-coequaliser→is-colimit {e} F {coequ} is-coeq =
  to-is-colimitp mc λ where
    {true} → refl
    {false} → refl
  where
    module is-coeq = is-coequaliser is-coeq
    open make-is-colimit

    mc : make-is-colimit F e
    mc .ψ true = coequ
    mc .ψ false = coequ ∘ forkl F
    mc .commutes {true} {true} tt = elimr (F .F-id)
    mc .commutes {false} {true} true = sym (is-coeq .coequal)
    mc .commutes {false} {true} false = refl
    mc .commutes {false} {false} tt = elimr (F .F-id)
    mc .universal eta p =
      is-coeq.universal (p {false} {true} false ∙ sym (p {false} {true} true))
    mc .factors {true} eta p =
      is-coeq.factors
    mc .factors {false} eta p =
      pulll is-coeq.factors ∙ p {false} {true} false
    mc .unique eta p other q =
      is-coeq.unique (q true)

is-colimit→is-coequaliser
  : ∀ (F : Functor ·⇉· C) {K : Functor ⊤Cat C}
  → {eta : F => K F∘ !F}
  → is-lan !F F K eta
  → is-coequaliser C (forkl F) (forkr F) (eta .η true)
is-colimit→is-coequaliser F {K} {eta} colim = co where
  module colim = is-colimit colim

  parallel
    : ∀ {x} → Hom (F .F₀ true) x
    → (j : Bool) → Hom (F .F₀ j) x
  parallel e' true = e'
  parallel e' false = e' ∘ forkl F

  parallel-commutes
    : ∀ {x} {e' : Hom (F .F₀ true) x}
    → e' ∘ forkl F ≡ e' ∘ forkr F
    → ∀ i j → (h : ·⇉· .Precategory.Hom i j)
    → parallel e' j ∘ F .F₁ {i} {j} h ≡ parallel e' i
  parallel-commutes p true true tt = elimr (F .F-id)
  parallel-commutes p false true true = sym p
  parallel-commutes p false true false = refl
  parallel-commutes p false false tt = elimr (F .F-id)

  co : is-coequaliser C (forkl F) (forkr F) (eta .η true)
  co .coequal =
    eta .is-natural false true false ∙ sym (eta .is-natural false true true)
  co .universal {e' = e'} p =
    colim.universal (parallel e') (λ {i} {j} h → parallel-commutes p i j h)
  co .factors = colim.factors {j = true} _ _
  co .unique {p = p} {colim = other} q =
    colim.unique _ _ _ λ where
      true → q
      false →
        ap (other ∘_) (introl (K .F-id) ∙ sym (eta .is-natural false true true))
        ·· pulll q
        ·· sym p

Coequaliser→Colimit : ∀ {F : Functor ·⇉· C} → Coequaliser C (forkl F) (forkr F) → Colimit F
Coequaliser→Colimit {F = F} coeq = to-colimit (is-coequaliser→is-colimit F (has-is-coeq coeq))

Colimit→Coequaliser : ∀ {a b} {f g : Hom a b} → Colimit {C = C} (Fork f g) → Coequaliser C f g
Colimit→Coequaliser colim .coapex = _
Colimit→Coequaliser colim .coeq = _
Colimit→Coequaliser {f = f} {g} colim .has-is-coeq =
  is-colimit→is-coequaliser (Fork f g) (Colimit.has-colimit colim)
```
