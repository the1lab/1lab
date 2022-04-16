```agda
open import Cat.Instances.Shape.Cospan
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Prelude

open import Data.Bool

module Cat.Diagram.Limit.Pullback {o h} (Cat : Precategory o h) where
```

We establish the correspondence between `Pullback`{.Agda} and the
`Limit`{.Agda} of a cospan diagram.

<!--
```agda
open import Cat.Reasoning Cat
open import Cat.Univalent Cat

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
  : ∀ {P A B C}
  → (p1 : Hom P A) (p2 : Hom P B)
    (f : Hom A C) (g : Hom B C)
  → f ∘ p1 ≡ g ∘ p2
  → Cone (cospan→cospan-diagram {C = Cat} f g)
Square→Cone p1 p2 f g square .apex = _
Square→Cone p1 p2 f g square .ψ cs-a = p1
Square→Cone p1 p2 f g square .ψ cs-b = p2
Square→Cone p1 p2 f g square .ψ cs-c = f ∘ p1
Square→Cone p1 p2 f g square .commutes {cs-a} {cs-a} tt = idl _
Square→Cone p1 p2 f g square .commutes {cs-a} {cs-c} tt = refl
Square→Cone p1 p2 f g square .commutes {cs-b} {cs-b} tt = idl _
Square→Cone p1 p2 f g square .commutes {cs-b} {cs-c} tt = sym square
Square→Cone p1 p2 f g square .commutes {cs-c} {cs-c} tt = idl _

Pullback→Limit
  : ∀ {A B C} {f : Hom A C} {g : Hom B C}
  → Pullback Cat f g
  → Limit (cospan→cospan-diagram {C = Cat} f g)
Pullback→Limit {f = f} {g} pb = lim where
  module pb = Pullback pb
  lim : Limit _
  lim .top = Square→Cone _ _ _ _ pb.square
  lim .has⊤ cone .centre .hom      = pb.limiting (cone .commutes tt ∙ sym (cone .commutes {cs-b} {cs-c} tt))
  lim .has⊤ cone .centre .commutes cs-a = pb.p₁∘limiting
  lim .has⊤ cone .centre .commutes cs-b = pb.p₂∘limiting
  lim .has⊤ cone .centre .commutes cs-c = pullr pb.p₁∘limiting ∙ cone .commutes tt
  lim .has⊤ cone .paths otherhom = Cone-hom-path _ (sym (pb.unique (otherhom .commutes _) (otherhom .commutes _)))

Limit→Pullback
  : ∀ {A B C}
  → {f : Hom A C} {g : Hom B C}
  → Limit (cospan→cospan-diagram {C = Cat} f g)
  → Pullback Cat f g
Limit→Pullback {f = f} {g} lim = pb where
  module lim = Terminal lim
  pb : Pullback Cat _ _
  pb .apex = lim.top .apex
  pb .p₁ = lim.top .ψ cs-a
  pb .p₂ = lim.top .ψ cs-b
  pb .has-is-pb .square = lim.top .commutes tt ∙ sym (lim.top .commutes {cs-b} {cs-c} tt)
  pb .has-is-pb .limiting x = lim.has⊤ (Square→Cone _ _ _ _ x) .centre .hom
  pb .has-is-pb .p₁∘limiting {p = p} = lim.has⊤ (Square→Cone _ _ _ _ p) .centre .commutes cs-a
  pb .has-is-pb .p₂∘limiting {p = p} = lim.has⊤ (Square→Cone _ _ _ _ p) .centre .commutes cs-b
  pb .has-is-pb .unique {p₁' = p₁'} {p₂'} {p} {lim'} a b =
    sym (ap hom (lim.has⊤ (Square→Cone _ _ _ _ p) .paths other))
    where
      other : Cone-hom _ _ _
      other .hom = _
      other .commutes cs-a = a
      other .commutes cs-b = b
      other .commutes cs-c =
        lim.top .ψ cs-c ∘ lim'     ≡˘⟨ pulll (lim.top .commutes tt) ⟩
        f ∘ lim.top .ψ cs-a ∘ lim' ≡⟨ ap (f ∘_) a ⟩
        f ∘ p₁'                    ∎
```
