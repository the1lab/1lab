---
description: |
  Double categories.
---
<!--
```agda
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Double.Base where
```

# Double precategories

```agda
record Double-precategory (o ℓv ℓh ℓ2 : Level) : Type (lsuc (o ⊔ ℓv ⊔ ℓh ⊔ ℓ2)) where
  field
    -- Think of the vertical bit as a "normal" category
    V : Precategory o ℓv

    -- Horizontal data is given by a doubly-displayed category.
    -- We want to think of the objects of H as horizontal morphisms,
    -- and the morphisms of H as some sort of 2-cell.
    H : Displayed (V ×ᶜ V) ℓh ℓ2

```

```agda
  module V = Cat.Reasoning V
  module H = Displayed H
  -- Let's unpack some data and give things nicer names.
  open V
    using (Ob)
    renaming
      ( Hom to Vert
      ; Hom-set to Vert-set
      ; id to idᵛ
      ; _∘_ to _∘ᵛ_
      ; idl to idlᵛ
      ; idr to idrᵛ
      ; assoc to assocᵛ
      )

  -- Horizontal morphisms are given by objects of H.
  Horiz : Ob → Ob → Type ℓh
  Horiz x y = H.Ob[ x , y ]

  -- 2-cells are morphisms of H.
  Cell : ∀ {a b x y} → Vert a b → Horiz b y → Horiz a x → Vert x y → Type ℓ2
  Cell u f g v = H.Hom[ u , v ] g f

  -- Just from the category structure of H we get identity 2-cells in the horizontal direction
  idᵛ² : ∀ {x y} {f : Horiz x y} → Cell idᵛ f f idᵛ
  idᵛ² = H.id'

  -- Composition of 2-cells
  _∘_
    : ∀ {a0 b0 c0 a1 b1 c1}
    → {u : Vert b0 c0} {v : Vert b1 c1} {w : Vert a0 b0} {x : Vert a1 b1}
    → {f : Horiz c0 c1} {g : Horiz b0 b1} {h : Horiz a0 a1}
    → Cell u f g v → Cell w g h x
    → Cell (u ∘ᵛ w) f h (v ∘ᵛ x)
  _∘_ = H._∘'_

  -- We don't need to spend the time giving these types for intuition.
  open H
    renaming (Hom[_]-set to Cell-set; idl' to idlᵛ²; idr' to idrᵛ²; assoc' to assocᵛ²)

  field
    idʰ : ∀ {x} → Horiz x x
    _∘ʰ_ : ∀ {x y z} → Horiz y z → Horiz x y → Horiz x z
    idlʰ
      : ∀ {x y} (f : Horiz x y)
      → idʰ ∘ʰ f ≡ f
    idrʰ
      : ∀ {x y} (f : Horiz x y)
      → f ∘ʰ idʰ ≡ f
    assocʰ
      : ∀ {w x y z} (f : Horiz y z) (g : Horiz x y) (h : Horiz w x)
      → f ∘ʰ (g ∘ʰ h) ≡ (f ∘ʰ g) ∘ʰ h


    idʰ² : ∀ {x y} {u : Vert x y} → Cell u idʰ idʰ u
    _◆_
      : ∀ {a0 b0 a1 b1 a2 b2}
      → {u : Vert a0 b0} {v : Vert a1 b1} {w : Vert a2 b2}
      → {f : Horiz b1 b2} {g : Horiz b0 b1} {h : Horiz a1 a2} {i : Horiz a0 a1}
      → Cell v f h w → Cell u g i v
      → Cell u (f ∘ʰ g) (h ∘ʰ i) w

    idlʰ²
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz b0 b1} {g : Horiz a0 a1}
      → (α : Cell u f g v)
      → PathP (λ i → Cell u (idlʰ f i) (idlʰ g i) v) (idʰ² ◆ α) α
    idrʰ²
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz b0 b1} {g : Horiz a0 a1}
      → (α : Cell u f g v)
      → PathP (λ i → Cell u (idrʰ f i) (idrʰ g i) v) (α ◆ idʰ²) α
    assocʰ²
      : ∀ {a0 b0 a1 b1 a2 b2 a3 b3}
      → {u0 : Vert a0 b0} {u1 : Vert a1 b1} {u2 : Vert a2 b2} {u3 : Vert a3 b3}
      → {f0 : Horiz b0 b1} {f1 : Horiz b1 b2} {f2 : Horiz b2 b3}
      → {g0 : Horiz a0 a1} {g1 : Horiz a1 a2} {g2 : Horiz a2 a3}
      → (α : Cell u2 f2 g2 u3) (β : Cell u1 f1 g1 u2) (γ : Cell u0 f0 g0 u1)
      → PathP (λ i → Cell u0 (assocʰ f2 f1 f0 i) (assocʰ g2 g1 g0 i) u3) (α ◆ (β ◆ γ)) ((α ◆ β) ◆ γ)

    id-interchange
      : ∀ {x}
      → Path (Cell {x} idᵛ idʰ idʰ idᵛ) idᵛ² idʰ²
    interchange
      : ∀ {a0 b0 c0 a1 b1 c1 a2 b2 c2}
      → {u0 : Vert a0 b0} {v0 : Vert b0 c0}
      → {u1 : Vert a1 b1} {v1 : Vert b1 c1}
      → {u2 : Vert a2 b2} {v2 : Vert b2 c2}
      → {f0 : Horiz c0 c1} {f1 : Horiz c1 c2}
      → {g0 : Horiz b0 b1} {g1 : Horiz b1 b2}
      → {h0 : Horiz a0 a1} {h1 : Horiz a1 a2}
      → (α : Cell v1 f1 g1 v2)
      → (β : Cell u1 g1 h1 u2)
      → (γ : Cell v0 f0 g0 v1)
      → (δ : Cell u0 g0 h0 u1)
      → (α ∘ β) ◆ (γ ∘ δ) ≡ (α ◆ γ) ∘ (β ◆ δ)
```
