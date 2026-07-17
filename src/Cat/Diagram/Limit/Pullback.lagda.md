<!--
```agda
open import Cat.Instances.Shape.Cospan
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Limit.Pullback {o h} (Cat : Precategory o h) where
```

We establish the correspondence between `Pullback`{.Agda} and the
`Limit`{.Agda} of a cospan diagram.

<!--
```agda
open import Cat.Reasoning Cat

-- Yikes:
open is-pullback
open Terminal
open Cone-hom
open Pullback
open Functor
open Cone
```
-->

```agda
Square→Cone
  : ∀ {x y} {P} {F : Functor (·→·←· {x} {y}) Cat}
  → (p1 : Hom P (F .F₀ cs-a)) (p2 : Hom P (F .F₀ cs-b))
  → F .F₁ {cs-a} {cs-c} _ ∘ p1 ≡ F .F₁ {cs-b} {cs-c} _ ∘ p2
  → Cone F
Square→Cone p1 p2 square .apex = _
Square→Cone p1 p2 square .ψ cs-a = p1
Square→Cone p1 p2 square .ψ cs-b = p2
Square→Cone {F = F} p1 p2 square .ψ cs-c = F .F₁ _ ∘ p1
Square→Cone {F = F} p1 p2 square .commutes {cs-a} {cs-a} _ = eliml (F .F-id)
Square→Cone {F = F} p1 p2 square .commutes {cs-a} {cs-c} _ = refl
Square→Cone {F = F} p1 p2 square .commutes {cs-b} {cs-b} _ = eliml (F .F-id)
Square→Cone {F = F} p1 p2 square .commutes {cs-b} {cs-c} _ = sym square
Square→Cone {F = F} p1 p2 square .commutes {cs-c} {cs-c} _ = eliml (F .F-id)

Pullback→Terminal-cone
  : ∀ {x y} {A B C} {f : Hom A C} {g : Hom B C}
  → Pullback Cat f g
  → Terminal (Cones (cospan→cospan-diagram x y {C = Cat} f g))
Pullback→Terminal-cone {f = f} {g} pb = lim where
  module pb = Pullback pb
  lim : Terminal (Cones _)
  lim .top = Square→Cone _ _ pb.square
  lim .has⊤ cone .centre .map      = pb.universal (cone .commutes (lift tt) ∙ sym (cone .commutes {cs-b} {cs-c} (lift tt)))
  lim .has⊤ cone .centre .com cs-a = pb.p₁∘universal
  lim .has⊤ cone .centre .com cs-b = pb.p₂∘universal
  lim .has⊤ cone .centre .com cs-c = pullr pb.p₁∘universal ∙ cone .commutes (lift tt)
  lim .has⊤ cone .paths otherhom = Cone-hom-path _ $ pb.unique
    (otherhom .com _)
    (otherhom .com _)

Terminal-cone→Pullback
  : ∀ {x y}
  → {F : Functor (·→·←· {x} {y}) Cat}
  → Terminal (Cones F)
  → Pullback Cat (F .F₁ {cs-a} {cs-c} _) (F .F₁ {cs-b} {cs-c} _)
Terminal-cone→Pullback {F = F} lim = pb where
  module lim = Terminal lim
  pb : Pullback Cat _ _
  pb .apex = lim.top .apex
  pb .p₁ = lim.top .ψ cs-a
  pb .p₂ = lim.top .ψ cs-b
  pb .has-is-pb .square = lim.top .commutes _ ∙ sym (lim.top .commutes {cs-b} {cs-c} _)
  pb .has-is-pb .universal x = lim.has⊤ (Square→Cone _ _ x) .centre .map
  pb .has-is-pb .p₁∘universal {p = p} = lim.has⊤ (Square→Cone _ _ p) .centre .com cs-a
  pb .has-is-pb .p₂∘universal {p = p} = lim.has⊤ (Square→Cone _ _ p) .centre .com cs-b
  pb .has-is-pb .unique {p₁' = p₁'} {p₂'} {p} {lim'} a b =
    ap map (lim.has⊤ (Square→Cone _ _ p) .paths other)
    where
      other : Cone-hom _ _ _
      other .map = _
      other .com cs-a = a
      other .com cs-b = b
      other .com cs-c =
        lim.top .ψ cs-c ∘ lim'                         ≡˘⟨ pulll (lim.top .commutes _) ⟩
        F .F₁ {cs-a} {cs-c} _ ∘ lim.top .ψ cs-a ∘ lim' ≡⟨ ap (_ ∘_) a ⟩
        F .F₁ {cs-a} {cs-c} _ ∘ p₁'                    ∎

Limit→Pullback
  : ∀ {x y} {a b c} → {f : Hom a c} {g : Hom b c}
  → Limit (cospan→cospan-diagram x y f g)
  → Pullback Cat f g
Limit→Pullback x = Terminal-cone→Pullback (Limit→Terminal-cone _ x)

Pullback→Limit
  : ∀ {x y} {A B C} {f : Hom A C} {g : Hom B C}
  → Pullback Cat f g
  → Limit (cospan→cospan-diagram x y {C = Cat} f g)
Pullback→Limit x = Terminal-cone→Limit _ (Pullback→Terminal-cone x)
```
