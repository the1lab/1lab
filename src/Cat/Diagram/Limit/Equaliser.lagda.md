```agda
open import Cat.Instances.Shape.Parallel
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Diagram.Equaliser
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Functor.Kan.Right
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Limit.Equaliser {o h} (Cat : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning Cat

open make-is-limit
open is-equaliser
open Equaliser
open Terminal
open Cone-hom
open Functor
open Cone
open Ran
```
-->

We establish the correspondence between `Equaliser`{.Agda} and the
`Limit`{.Agda} of a [parallel arrows] diagram.

[parallel arrows]: Cat.Instances.Shape.Parallel.html

```agda
Fork→Cone
  : ∀ {E} (F : Functor ·⇉· Cat)
  → (eq : Hom E (F .F₀ false))
  → F .F₁ {false} {true} false ∘ eq ≡ F .F₁ {false} {true} true ∘ eq
  → Cone F
Fork→Cone F eq p .apex     = _
Fork→Cone F eq p .ψ false  = eq
Fork→Cone F eq p .ψ true   = F .F₁ false ∘ eq
Fork→Cone F eq p .commutes {false} {false} tt    = eliml (F .F-id)
Fork→Cone F eq p .commutes {false} {true}  false = refl
Fork→Cone F eq p .commutes {false} {true}  true  = sym p
Fork→Cone F eq p .commutes {true}  {true}  tt    = eliml (F .F-id)

Equaliser→Limit
  : ∀ {F : Functor ·⇉· Cat}
  → Equaliser Cat (F .F₁ {false} {true} false) (F .F₁ true)
  → Limit F
Equaliser→Limit {F = F} eq = lim where
  module eq = Equaliser eq
  lim : Limit _
  lim .Ext = const! eq.apex
  lim .has-ran = to-is-limit mk where
    mk : make-is-limit _ _
    mk .ψ true  = F .F₁ false ∘ eq.equ
    mk .ψ false = eq.equ
    mk .commutes {true}  {true}  tt    = eliml (F .F-id)
    mk .commutes {false} {true}  true  = sym eq.equal
    mk .commutes {false} {true}  false = refl
    mk .commutes {false} {false} tt    = eliml (F .F-id)

    mk .universal eta p
      = eq.limiting (p {x = false} {true} false ∙ sym (p {x = false} {true} true))
    mk .factors {j = true} eta p  = pullr eq.universal ∙ p false
    mk .factors {j = false} eta p = eq.universal
    mk .unique eta p other q      = eq.unique (sym (q false))

Limit→Equaliser
  : ∀ {F : Functor ·⇉· Cat}
  → Limit F
  → Equaliser Cat (F .F₁ {false} {true} false) (F .F₁ true)
Limit→Equaliser {F} lim = eq where
  module lim = is-limit (lim .has-ran)
  eq : Equaliser Cat _ _
  eq .apex = _
  eq .equ = lim.ψ false
  eq .has-is-eq .equal = lim.commutes {false} {true} false ∙ sym (lim.commutes true)
  eq .has-is-eq .limiting {e′ = e′} p = lim.universal
    (λ { true  → F .F₁ true ∘ e′
       ; false → e′
       })
    λ { {true}  {true} t     → eliml (F .F-id)
      ; {false} {true} true  → refl
      ; {false} {true} false → p
      ; {false} {false} t    → eliml (F .F-id)
      }
  eq .has-is-eq .universal {p = p} = lim.factors _ _
  eq .has-is-eq .unique {e′ = e′} {p = p} {lim' = lim′} x = lim.unique _ _ lim′ λ where
    true → sym $
      F .F₁ true ∘ e′             ≡⟨ ap (_ ∘_) x ⟩
      F .F₁ true ∘ eq .equ ∘ lim′ ≡⟨ pulll (lim.commutes true) ⟩
      lim.ψ true ∘ lim′           ∎
    false → sym x
```
