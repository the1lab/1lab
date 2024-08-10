---
description: |
  Double categories.
---
<!--
```agda
open import Cat.Prelude
```
-->
```agda
module Cat.Double.Base where
```

# Double categories

```agda
record Double-precategory (o ℓv ℓh ℓc : Level) : Type (lsuc (o ⊔ ℓv ⊔ ℓh ⊔ ℓc)) where
  no-eta-equality
  field
    Ob : Type o
    Vert : Ob → Ob → Type ℓv
    Horiz : Ob → Ob → Type ℓh
    Cell : ∀ {a b c d : Ob} → Horiz a b → Vert a c → Vert b d → Horiz c d → Type ℓc
    Vert-set : ∀ {a b} → is-set (Vert a b)
    Horiz-set : ∀ {a b} → is-set (Horiz a b)
    Cell-set
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1}
      → is-set (Cell f u v g)
```

Vertical 1-cells form a category.

```agda
    idv : ∀ {a} → Vert a a
    _∘v_ : ∀ {a b c} → Vert b c → Vert a b → Vert a c
    idvl
      : ∀ {a b}
      → (f : Vert a b)
      → idv ∘v f ≡ f
    idvr
      : ∀ {a b}
      → (f : Vert a b)
      → f ∘v idv ≡ f
    assocv
      : ∀ {a b c d}
      → (f : Vert c d) → (g : Vert b c) → (h : Vert a b)
      → f ∘v (g ∘v h) ≡ (f ∘v g) ∘v h
```

Horizontal 1-cells form a category.

```agda
    idh : ∀ {a} → Horiz a a
    _∘h_ : ∀ {a b c} → Horiz b c → Horiz a b → Horiz a c
    idhl
      : ∀ {a b}
      → (f : Horiz a b)
      → idh ∘h f ≡ f
    idhr
      : ∀ {a b}
      → (f : Horiz a b)
      → f ∘h idh ≡ f
    assoch
      : ∀ {a b c d}
      → (f : Horiz c d) → (g : Horiz b c) → (h : Horiz a b)
      → f ∘h (g ∘h h) ≡ (f ∘h g) ∘h h
```

We can vertically compose 2-cells, and this composition is associative
and unital.

```agda
    idv2
      : ∀ {a b} {f : Horiz a b}
      → Cell f idv idv f
    _∘_
      : ∀ {a0 b0 c0 a1 b1 c1}
      → {u : Vert b0 c0} {v : Vert b1 c1} {w : Vert a0 b0} {x : Vert a1 b1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1} {h : Horiz c0 c1}
      → Cell g u v h
      → Cell f w x g
      → Cell f (u ∘v w) (v ∘v x) h
    idv2l
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1}
      → (α : Cell f u v g)
      → PathP (λ i → Cell f (idvl u i) (idvl v i) g) (idv2 ∘ α) α
    idv2r
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1}
      → (α : Cell f u v g)
      → PathP (λ i → Cell f (idvr u i) (idvr v i) g) (α ∘ idv2) α
    assocv2
      : ∀ {a0 b0 c0 d0 a1 b1 c1 d1}
      → {u0 : Vert a0 b0} {v0 : Vert b0 c0} {w0 : Vert c0 d0}
      → {u1 : Vert a1 b1} {v1 : Vert b1 c1} {w1 : Vert c1 d1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1} {h : Horiz c0 c1} {k : Horiz d0 d1}
      → (α : Cell h w0 w1 k) (β : Cell g v0 v1 h) (γ : Cell f u0 u1 g)
      → PathP (λ i → Cell f (assocv w0 v0 u0 i) (assocv w1 v1 u1 i) k) (α ∘ (β ∘ γ)) ((α ∘ β) ∘ γ)
```

We can horizontally compose 2-cells, and this composition is associative
and unital.


```agda
    idh2
      : ∀ {a b} {u : Vert a b}
      → Cell idh u u idh
    _◆_
      : ∀ {a0 b0 a1 b1 a2 b2}
      → {u : Vert a0 b0} {v : Vert a1 b1} {w : Vert a2 b2}
      → {f : Horiz a1 a2} {g : Horiz a0 a1} {h : Horiz b1 b2} {i : Horiz b0 b1}
      → Cell f v w h
      → Cell g u v i
      → Cell (f ∘h g) u w (h ∘h i)
    idh2l
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1}
      → (α : Cell f u v g)
      → PathP (λ i → Cell (idhl f i) u v (idhl g i)) (idh2 ◆ α) α
    idh2r
      : ∀ {a0 b0 a1 b1}
      → {u : Vert a0 b0} {v : Vert a1 b1}
      → {f : Horiz a0 a1} {g : Horiz b0 b1}
      → (α : Cell f u v g)
      → PathP (λ i → Cell (idhr f i) u v (idhr g i)) (α ◆ idh2) α
    assoch2
      : ∀ {a0 b0 a1 b1 a2 b2 a3 b3}
      → {u0 : Vert a0 b0} {u1 : Vert a1 b1} {u2 : Vert a2 b2} {u3 : Vert a3 b3}
      → {f0 : Horiz a0 a1} {f1 : Horiz a1 a2} {f2 : Horiz a2 a3}
      → {g0 : Horiz b0 b1} {g1 : Horiz b1 b2} {g2 : Horiz b2 b3}
      → (α : Cell f2 u2 u3 g2) (β : Cell f1 u1 u2 g1) (γ : Cell f0 u0 u1 g0)
      → PathP (λ i → Cell (assoch f2 f1 f0 i) u0 u3 (assoch g2 g1 g0 i)) (α ◆ (β ◆ γ)) ((α ◆ β) ◆ γ)
```

We also have interchange laws relating horizontal and vertical composition.


```agda
    idv2-◆
      : ∀ {a b c}
      → (f : Horiz b c) (g : Horiz a b)
      → idv2 ◆ idv2 ≡ idv2 {f = f ∘h g}
    idh2-∘
      : ∀ {a b c}
      → (u : Vert b c) (v : Vert a b)
      → idh2 ∘ idh2 ≡ idh2 {u = u ∘v v}
    idvh2
      : ∀ {a}
      → idv2 {f = idh {a}} ≡ idh2 {u = idv {a}}
    interchange
      : ∀ {a0 b0 c0 a1 b1 c1 a2 b2 c2}
      → {u0 : Vert a0 b0} {v0 : Vert b0 c0}
      → {u1 : Vert a1 b1} {v1 : Vert b1 c1}
      → {u2 : Vert a2 b2} {v2 : Vert b2 c2}
      → {f0 : Horiz a0 a1} {f1 : Horiz a1 a2}
      → {g0 : Horiz b0 b1} {g1 : Horiz b1 b2}
      → {h0 : Horiz c0 c1} {h1 : Horiz c1 c2}
      → (α : Cell f0 u0 u1 g0)
      → (β : Cell f1 u1 u2 g1)
      → (γ : Cell g0 v0 v1 h0)
      → (δ : Cell g1 v1 v2 h1)
      → (δ ∘ β) ◆ (γ ∘ α) ≡ (δ ◆ γ) ∘ (β ◆ α)
```
