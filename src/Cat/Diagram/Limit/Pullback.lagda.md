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
module Cat.Diagram.Limit.Pullback {oc ℓc} (C : Precategory oc ℓc) where
```

We establish the correspondence between `Pullback`{.Agda} and the
`Limit`{.Agda} of a cospan diagram.

<!--
```agda
open import Cat.Reasoning C

-- Yikes:
open is-pullback
open Cone-hom
open Pullback
open Functor
open Cone
```
-->

```agda
Square→Cone
  : ∀ {x y} {P} {F : Functor (·→·←· {x} {y}) C}
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

module _
  {oj ℓj}
  (Dia : Functor (·→·←· {oj} {ℓj}) C)
  where

  private
    module Dia = Functor Dia

    a b c : Ob
    a = Dia.₀ cs-a
    b = Dia.₀ cs-b
    c = Dia.₀ cs-c

    f : Hom a c
    f = Dia.₁ (lift tt)

    g : Hom b c
    g = Dia.₁ (lift tt)

  Pullback→Terminal-cone
    : Pullback C f g
    → Terminal (Cones Dia)
  {-# INLINE Pullback→Terminal-cone #-}
  Pullback→Terminal-cone pb = to-terminal (record { Pullback→Terminal-cone }) where
    module Pullback→Terminal-cone where
      module pb = Pullback pb

      top : Cone Dia
      top = Square→Cone pb.p₁ pb.p₂ pb.square

      ! : ∀ {K : Cone Dia} → Cone-hom Dia K top
      ! {K} .map = pb.universal (K .commutes (lift tt) ∙ sym (K .commutes {cs-b} {cs-c} (lift tt)))
      ! {K} .com cs-a = pb.p₁∘universal
      ! {K} .com cs-b = pb.p₂∘universal
      ! {K} .com cs-c = pullr pb.p₁∘universal ∙ K .commutes (lift tt)

      !-unique : ∀ {K} (h : Cone-hom Dia K top) → h ≡ !
      !-unique h = Cone-hom-path Dia (pb.unique (h .com cs-a) (h .com cs-b))


  Terminal-cone→Pullback
    : Terminal (Cones Dia)
    → Pullback C f g
  Terminal-cone→Pullback lim = pb where
    module lim = Terminal lim
    pb : Pullback C _ _
    pb .apex = lim.top .apex
    pb .p₁ = lim.top .ψ cs-a
    pb .p₂ = lim.top .ψ cs-b
    pb .has-is-pb .square = lim.top .commutes _ ∙ sym (lim.top .commutes {cs-b} {cs-c} _)
    pb .has-is-pb .universal x = lim.! {Square→Cone _ _ x} .map
    pb .has-is-pb .p₁∘universal {p = p} = lim.! .com cs-a
    pb .has-is-pb .p₂∘universal {p = p} = lim.! .com cs-b
    pb .has-is-pb .unique {p₁' = p₁'} {p₂'} {p} {lim'} a b =
      ap map (lim.!-unique other)
      where
        other : Cone-hom _ _ _
        other .map = _
        other .com cs-a = a
        other .com cs-b = b
        other .com cs-c =
          lim.top .ψ cs-c ∘ lim'                         ≡˘⟨ pulll (lim.top .commutes _) ⟩
          Dia.₁ {cs-a} {cs-c} _ ∘ lim.top .ψ cs-a ∘ lim' ≡⟨ ap (_ ∘_) a ⟩
          Dia.₁ {cs-a} {cs-c} _ ∘ p₁'                    ∎

  Limit→Pullback
    : Limit Dia
    → Pullback C f g
  Limit→Pullback x = Terminal-cone→Pullback (Limit→Terminal-cone _ x)

  Pullback→Limit
    : Pullback C f g
    → Limit Dia
  Pullback→Limit x = Terminal-cone→Limit _ (Pullback→Terminal-cone x)
```
