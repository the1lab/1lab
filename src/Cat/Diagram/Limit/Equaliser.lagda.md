```agda
open import Cat.Instances.Shape.Parallel
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Limit.Equaliser {o h} (Cat : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning Cat
open import Cat.Univalent Cat

open is-equaliser
open Equaliser
open Terminal
open Cone-hom
open Functor
open Cone
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
  → Equaliser Cat (F .F₁ false) (F .F₁ true)
  → Limit F
Equaliser→Limit {F = F} eq = lim where
  module eq = Equaliser eq
  lim : Limit _
  lim .top = Fork→Cone F eq.equ eq.equal
  lim .has⊤ cone .centre .hom      =
    eq.limiting (cone .commutes {false} {true} false ∙ sym (cone .commutes true))
  lim .has⊤ cone .centre .commutes false = eq.universal
  lim .has⊤ cone .centre .commutes true = pullr eq.universal ∙ cone .commutes {false} {true} false
  lim .has⊤ cone .paths other = Cone-hom-path _ (sym (eq.unique p)) where
    p : cone .ψ false ≡ eq .equ ∘ other .hom
    p = sym (other .commutes _)

Limit→Equaliser
  : ∀ {F : Functor ·⇉· Cat}
  → Limit F
  → Equaliser Cat (F .F₁ {false} {true} false) (F .F₁ true)
Limit→Equaliser {F} lim = eq where
  module lim = Terminal lim
  eq : Equaliser Cat _ _
  eq .apex = _
  eq .equ = lim.top .ψ false
  eq .has-is-eq .equal =
    lim.top .commutes {false} {true} false ∙ sym (lim.top .commutes true)
  eq .has-is-eq .limiting p = lim.has⊤ (Fork→Cone _ _ p) .centre .hom
  eq .has-is-eq .universal {p = p} =
    lim.has⊤ (Fork→Cone _ _ p) .centre .commutes false
  eq .has-is-eq .unique {e′ = e'} {p = p} {lim' = lim'} x =
    sym (ap hom (lim.has⊤ (Fork→Cone _ _ p) .paths other))
    where
      other : Cone-hom _ _ _
      other .hom = _
      other .commutes false = sym x
      other .commutes true = sym (
        F .F₁ false ∘ e'                      ≡⟨ ap (_ ∘_) x ⟩
        F .F₁ false ∘ lim.top .ψ false ∘ lim' ≡⟨ pulll (lim.top .commutes false) ⟩
        lim.top .ψ true ∘ lim'                ∎
        )
```
