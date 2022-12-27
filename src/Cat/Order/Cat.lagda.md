```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Instances.StrictCat
open import Cat.Instances.Functor
open import Cat.Order.Base
open import Cat.Prelude

module Cat.Order.Cat where
```

```agda
to-category : ∀ {ℓ ℓ′} → Posets.Ob → Precategory ℓ ℓ′
to-category P = cat module poset-to-category where
  module P = Poset P
  open Precategory

  cat : Precategory _ _
  cat .Ob      = P.Ob
  cat .Hom     = P._≤_
  cat .id      = P.≤-refl _
  cat ._∘_ f g = P.≤-trans _ _ _ g f
  cat .idr f   = P.≤-thin _ _ _ _
  cat .idl f   = P.≤-thin _ _ _ _
  cat .assoc f g h = P.≤-thin _ _ _ _
  cat .Hom-set x y = is-prop→is-set (P.≤-thin x y)

{-# DISPLAY poset-to-category.cat P = to-category P #-}

open Functor
Posets↪Strict-cats : ∀ {ℓ ℓ′} → Functor (Posets ℓ ℓ′) (Strict-cats ℓ ℓ′)
Posets↪Strict-cats .F₀ P = to-category P , Poset.has-is-set P

Posets↪Strict-cats .F₁ f .F₀ = f .hom
Posets↪Strict-cats .F₁ f .F₁ = f .preserves _ _
Posets↪Strict-cats .F₁ {y = y} f .F-id    = Poset.≤-thin y _ _ _ _
Posets↪Strict-cats .F₁ {y = y} f .F-∘ g h = Poset.≤-thin y _ _ _ _

Posets↪Strict-cats .F-id    = Functor-path (λ _ → refl) λ _ → refl
Posets↪Strict-cats .F-∘ f g = Functor-path (λ _ → refl) λ _ → refl
```
