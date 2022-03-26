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
  : ∀ {E A B}
  → (eq : Hom E A) (f g : Hom A B)
  → f ∘ eq ≡ g ∘ eq
  → Cone (par-arrows→par-diagram {C = Cat} f g)
Fork→Cone eq f g p .apex     = _
Fork→Cone eq f g p .ψ false  = eq
Fork→Cone eq f g p .ψ true   = f ∘ eq
Fork→Cone eq f g p .commutes {false} {false} tt    = idl _
Fork→Cone eq f g p .commutes {false} {true}  false = refl
Fork→Cone eq f g p .commutes {false} {true}  true  = sym p
Fork→Cone eq f g p .commutes {true}  {true}  tt    = idl _

Equaliser→Limit
  : ∀ {A B} {f g : Hom A B}
  → Equaliser Cat f g
  → Limit (par-arrows→par-diagram {C = Cat} f g)
Equaliser→Limit {f = f} {g = g} eq = lim where
  module eq = Equaliser eq
  lim : Limit _
  lim .top = Fork→Cone eq.equ f g eq.equal
  lim .has⊤ cone .centre .hom      =
    eq.limiting (cone .commutes {false} {true} false ∙ sym (cone .commutes true))
  lim .has⊤ cone .centre .commutes {false} = eq.universal
  lim .has⊤ cone .centre .commutes {true} = pullr eq.universal ∙ cone .commutes {false} {true} false
  lim .has⊤ cone .paths other = Cone-hom-path _ (sym (eq.unique p)) where
    p : cone .ψ false ≡ eq .equ ∘ other .hom
    p = sym (other .commutes)

Limit→Equaliser
  : ∀ {A B} {f g : Hom A B}
  → Limit (par-arrows→par-diagram {C = Cat} f g)
  → Equaliser Cat f g
Limit→Equaliser {f = f} {g} lim = eq where
  module lim = Terminal lim
  eq : Equaliser Cat f g
  eq .apex = _
  eq .equ = lim.top .ψ false
  eq .has-is-eq .equal =
    lim.top .commutes {false} {true} false ∙ sym (lim.top .commutes true)
  eq .has-is-eq .limiting p = lim.has⊤ (Fork→Cone _ _ _ p) .centre .hom
  eq .has-is-eq .universal {p = p} =
    lim.has⊤ (Fork→Cone _ _ _ p) .centre .commutes {false}
  eq .has-is-eq .unique {e′ = e'} {p = p} {lim' = lim'} x =
    sym (ap hom (lim.has⊤ (Fork→Cone _ _ _ p) .paths other))
    where
      other : Cone-hom _ _ _
      other .hom = _
      other .commutes {false} = sym x
      other .commutes {true} = sym (
        f ∘ e'                      ≡⟨ ap (f ∘_) x ⟩
        f ∘ lim.top .ψ false ∘ lim' ≡⟨ pulll (lim.top .commutes false) ⟩
        lim.top .ψ true ∘ lim'      ∎
        )
```
