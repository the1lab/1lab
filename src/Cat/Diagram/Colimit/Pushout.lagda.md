<!--
```agda
open import Cat.Diagram.Colimit.Cocone
open import Cat.Instances.Shape.Cospan
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Initial
open import Cat.Diagram.Pushout
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Colimit.Pushout {o h} (𝒞 : Precategory o h) where
```

We establish the correspondence between `Pushout`{.Agda} and the
`Colimit`{.Agda} of a span diagram.

<!--
```agda
open import Cat.Reasoning 𝒞

open is-pushout
open Cocone-hom
open Initial
open Pushout
open Functor
open Cocone
```
-->

```agda
Square→Cocone
  : ∀ {x y} {P} {F : Functor (·←·→· {x} {y}) 𝒞}
  → (p1 : Hom (F .F₀ cs-a) P) (p2 : Hom (F .F₀ cs-b) P)
  → p1 ∘ F .F₁ {cs-c} {cs-a} _ ≡ p2 ∘ F .F₁ {cs-c} {cs-b} _
  → Cocone F
Square→Cocone p1 p2 square .coapex = _
Square→Cocone p1 p2 square .ψ cs-a = p1
Square→Cocone p1 p2 square .ψ cs-b = p2
Square→Cocone {F = F} p1 p2 square .ψ cs-c = p1 ∘ F .F₁ _
Square→Cocone {F = F} p1 p2 square .commutes {cs-a} {cs-a} _ = elimr (F .F-id)
Square→Cocone {F = F} p1 p2 square .commutes {cs-c} {cs-a} _ = refl
Square→Cocone {F = F} p1 p2 square .commutes {cs-b} {cs-b} _ = elimr (F .F-id)
Square→Cocone {F = F} p1 p2 square .commutes {cs-c} {cs-b} _ = sym square
Square→Cocone {F = F} p1 p2 square .commutes {cs-c} {cs-c} _ = elimr (F .F-id)

Pushout→Initial-cocone
  : ∀ {x y} {A B C} {f : Hom C A} {g : Hom C B}
  → Pushout 𝒞 f g
  → Initial (Cocones (span→span-diagram x y {C = 𝒞} f g))
Pushout→Initial-cocone {f = f} {g} po = colim where
  module po = Pushout po
  colim : Initial (Cocones _)
  colim .bot = Square→Cocone _ _ po.square
  colim .has⊥ cc .centre .map      = po.universal (cc .commutes {cs-c} {cs-a} (lift tt) ∙ sym (cc .commutes {cs-c} {cs-b} (lift tt)))
  colim .has⊥ cc .centre .com cs-a = po.universal∘i₁
  colim .has⊥ cc .centre .com cs-b = po.universal∘i₂
  colim .has⊥ cc .centre .com cs-c = pulll po.universal∘i₁ ∙ cc .commutes (lift tt)
  colim .has⊥ cc .paths otherhom = Cocone-hom-path _ (po.unique (otherhom .com _) (otherhom .com _))

Initial-cocone→Pushout
  : ∀ {x y}
  → {F : Functor (·←·→· {x} {y}) 𝒞}
  → Initial (Cocones F)
  → Pushout 𝒞 (F .F₁ {cs-c} {cs-a} _) (F .F₁ {cs-c} {cs-b} _)
Initial-cocone→Pushout {F = F} colim = po where
  module colim = Initial colim
  po : Pushout 𝒞 _ _
  po .coapex = colim.bot .coapex
  po .i₁ = colim.bot .ψ cs-a
  po .i₂ = colim.bot .ψ cs-b
  po .has-is-po .square = colim.bot .commutes _ ∙ sym (colim.bot .commutes {cs-c} {cs-b} _)
  po .has-is-po .universal x = colim.has⊥ (Square→Cocone _ _ x) .centre .map
  po .has-is-po .universal∘i₁ {p = p} = colim.has⊥ (Square→Cocone _ _ p) .centre .com cs-a
  po .has-is-po .universal∘i₂ {p = p} = colim.has⊥ (Square→Cocone _ _ p) .centre .com cs-b
  po .has-is-po .unique {i₁' = i₁'} {i₂'} {p} {colim'} a b =
    ap map (colim.has⊥ (Square→Cocone _ _ p) .paths other)
    where
      other : Cocone-hom _ _ _
      other .map = _
      other .com cs-a = a
      other .com cs-b = b
      other .com cs-c =
        colim' ∘ colim.bot .ψ cs-c                         ≡˘⟨ cdr (colim.bot .commutes _) ⟩
        colim' ∘ colim.bot .ψ cs-a ∘ F .F₁ {cs-c} {cs-a} _ ≡⟨ pulll a ⟩
        i₁' ∘ F .F₁ {cs-c} {cs-a} _                        ∎

Colimit→Pushout
  : ∀ {x y} {a b c} → {f : Hom c a} {g : Hom c b}
  → Colimit (span→span-diagram x y f g)
  → Pushout 𝒞 f g
Colimit→Pushout x = Initial-cocone→Pushout (Colimit→Initial-cocone _ x)

Pushout→Colimit
  : ∀ {x y} {A B C} {f : Hom C A} {g : Hom C B}
  → Pushout 𝒞 f g
  → Colimit (span→span-diagram x y {C = 𝒞} f g)
Pushout→Colimit x = Initial-cocone→Colimit _ (Pushout→Initial-cocone x)
```
