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

import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->
```agda
module Cat.Double.Base where
```

# Double precategories

```agda
record Double-precategory-on
  {o ℓ₀ ℓ₁ ℓ₂}
  {D₀ : Precategory o ℓ₀}
  (D₁ : Displayed (D₀ ×ᶜ D₀) ℓ₁ ℓ₂)
  : Type (o ⊔ ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
  where
  private
    module D₀ = Cat.Reasoning D₀
    module D₁ = Displayed D₁

  open D₀ renaming (Hom to Tight; Hom-set to Tight-set) public

  Loose : Ob → Ob → Type ℓ₁
  Loose x y = D₁.Ob[ x , y ]

  Cell : ∀ {a b x y} → Tight a b → Loose a x → Loose b y → Tight x y → Type _
  Cell u f g v = D₁.Hom[ u , v ] f g
```

```agda
  id₂ : ∀ {x y} {f : Loose x y} → Cell id f f id
  id₂ = D₁.id'

  _∘₂_
    : ∀ {a0 b0 c0 a1 b1 c1}
    → {f : Tight b0 c0} {g : Tight a0 b0} {h : Tight b1 c1} {k : Tight a1 b1}
    → {p : Loose a0 a1} {q : Loose b0 b1} {r : Loose c0 c1}
    → Cell f q r h
    → Cell g p q k
    → Cell (f ∘ g) p r (h ∘ k)
  _∘₂_ = D₁._∘'_

  open D₁
    hiding (id'; _∘'_)
    renaming (Hom[_]-set to Cell-set; idl' to ∘-idl; idr' to ∘-idr; assoc' to ∘-assoc)
  open Cat.Displayed.Morphism D₁
```

```agda
  field
    id⇸₁ : ∀ {x} → Loose x x
    id⇸₂ : ∀ {x y} {f : Tight x y} → Cell f id⇸₁ id⇸₁ f
    id-interchange : ∀ {x} → id⇸₂ {x} ≡ id₂ {x}
```

```agda
  field
    _⊗₁_ : ∀ {x y z} → Loose x y → Loose y z → Loose x z
    _⊗₂_
      : ∀ {a0 b0 a1 b1 a2 b2}
      → {f : Tight a0 b0} {g : Tight a1 b1} {h : Tight a2 b2}
      → {p : Loose a0 a1} {q : Loose a1 a2} {r : Loose b0 b1} {s : Loose b1 b2}
      → Cell f p r g
      → Cell g q s h
      → Cell f (p ⊗₁ q) (r ⊗₁ s) h
    interchange
      : ∀ {a0 b0 c0 a1 b1 c1 a2 b2 c2}
      → {f0 : Tight b0 c0} {g0 : Tight a0 b0}
      → {f1 : Tight b1 c1} {g1 : Tight a1 b1}
      → {f2 : Tight b2 c2} {g2 : Tight a2 b2}
      → {p0 : Loose a0 a1} {p1 : Loose a1 a2}
      → {q0 : Loose b0 b1} {q1 : Loose b1 b2}
      → {r0 : Loose c0 c1} {r1 : Loose c1 c2}
      → (α : Cell f0 q0 r0 f1)
      → (β : Cell g0 p0 q0 g1)
      → (γ : Cell f1 q1 r1 f2)
      → (δ : Cell g1 p1 q1 g2)
      → (α ∘₂ β) ⊗₂ (γ ∘₂ δ) ≡ (α ⊗₂ γ) ∘₂ (β ⊗₂ δ)
```

```agda
  field
    unitorl : ∀ {x y} (f : Loose x y) → (id⇸₁ ⊗₁ f) ≅↓ f
    unitorr : ∀ {x y} (f : Loose x y) → (f ⊗₁ id⇸₁) ≅↓ f
    associator : ∀ {w x y z} (f : Loose w x) (g : Loose x y) (h : Loose y z) → (f ⊗₁ (g ⊗₁ h)) ≅↓ ((f ⊗₁ g) ⊗₁ h)

  module λ⇸ {x y} (f : Loose x y) = _≅[_]_ (unitorl f)
  module ρ⇸ {x y} (f : Loose x y) = _≅[_]_ (unitorr f)
  module α⇸ {w x y z} (f : Loose w x) (g : Loose x y) (h : Loose y z) = _≅[_]_ (associator f g h)

  infixr 20 _⊗₁_
  infixr 40 _⊗₂_
  infixr 20 _∘₂_
```

```agda
  field
    triangle
      : ∀ {x}
      → PathP (λ i → Cell {x} (idl id i) (id⇸₁ ⊗₁ (id⇸₁ ⊗₁ id⇸₁)) ((id⇸₁ ⊗₁ id⇸₁) ⊗₁ id⇸₁) (idl id i))
        (ρ⇸.from' (id⇸₁ ⊗₁ id⇸₁) ∘₂ λ⇸.to' (id⇸₁ ⊗₁ id⇸₁))
        (α⇸.to' id⇸₁ id⇸₁ id⇸₁)
    pentagon
      : ∀ {v w x y z} {p : Loose v w} {q : Loose w x} {r : Loose x y} {s : Loose y z}
      → PathP (λ i → Cell (idl (id ∘ id) i) (p ⊗₁ (q ⊗₁ (r ⊗₁ s))) (((p ⊗₁ q) ⊗₁ r) ⊗₁ s) (idl (id ∘ id) i))
        (α⇸.to' p q r ⊗₂ id₂ ∘₂ α⇸.to' p (q ⊗₁ r) s ∘₂ id₂ ⊗₂ α⇸.to' q r s)
        (α⇸.to' (p ⊗₁ q) r s ∘₂ α⇸.to' p q (r ⊗₁ s))
```
