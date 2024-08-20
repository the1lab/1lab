---
description: |
  Functorial factorisation systems.
---
<!--
```agda
open import Cat.Displayed.Instances.Factorisations
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Instances.Comma
open import Cat.Displayed.Total
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Morphism.Factorisation.Functorial where
```

# Functorial factorisation systems

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  open Total-hom
  open Functor
  open _=>_
```
-->

```agda
  record Functorial-factorisation : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      {fac} : ∀ {x y} → Hom x y → Ob
      left  : ∀ {x y} → (f : Hom x y) → Hom x (fac f)
      right : ∀ {x y} → (f : Hom x y) → Hom (fac f) y
      factors : ∀ {x y} {f : Hom x y} → right f ∘ left f ≡ f
      split
        : ∀ {a b x y}
        → {f : Hom a b}  {g : Hom x y}
        → (k : Hom b y) (h : Hom a x)
        → k ∘ f ≡ g ∘ h
        → Hom (fac f) (fac g)
      squarel
        : ∀ {a b x y}
        → {f : Hom a b} {k : Hom b y} {h : Hom a x} {g : Hom x y}
        → {p : k ∘ f ≡ g ∘ h}
        → split k h p ∘ left f ≡ left g ∘ h
      squarer
        : ∀ {a b x y}
        → {f : Hom a b} {k : Hom b y} {h : Hom a x} {g : Hom x y}
        → {p : k ∘ f ≡ g ∘ h}
        → k ∘ right f ≡ right g ∘ split k h p
      split-id
        : ∀ {x y} {f : Hom x y} → (p : id ∘ f ≡ f ∘ id) → split id id p ≡ id
      split-∘
        : ∀ {a b m n x y}
        → {f : Hom a b} {g : Hom m n} {h : Hom x y}
        → {k1 : Hom n y} {k2 : Hom b n} {l1 : Hom m x} {l2 : Hom a m}
        → (p : (k1 ∘ k2) ∘ f ≡ h ∘ l1 ∘ l2) (q : k1 ∘ g ≡ h ∘ l1) (r : k2 ∘ f ≡ g ∘ l2)
        → split (k1 ∘ k2) (l1 ∘ l2) p ≡ (split k1 l1 q ∘ split k2 l2 r)
```

```agda
    FactorF : Lifting (Factorisations C) Id
    FactorF .Lifting.F₀' ((x , y) , f) .Factor.fac = fac f
    FactorF .Lifting.F₀' ((x , y) , f) .Factor.left = left f
    FactorF .Lifting.F₀' ((x , y) , f) .Factor.right = right f
    FactorF .Lifting.F₀' ((x , y) , f) .Factor.factors = factors
    FactorF .Lifting.F₁' α .Factor-hom.split =
      split (α .hom .snd) (α .hom .fst) (sym (α .preserves))
    FactorF .Lifting.F₁' α .Factor-hom.squarel = squarel
    FactorF .Lifting.F₁' α .Factor-hom.squarer = squarer
    FactorF .Lifting.F-id' = Factor-hom-pathp (split-id _)
    FactorF .Lifting.F-∘' α β = Factor-hom-pathp (split-∘ _ _ _)
```

```agda
    -- Actually a vertical endofunctor on coslices!
    Left : Functor (∫ (Arrows C)) (∫ (Arrows C))
    Left .F₀ ((x , y) , f) = (x , fac f) , left f
    Left .F₁ α .hom =
      α .hom .fst ,
      split (α .hom .snd) (α .hom .fst) (sym (α .preserves))
    Left .F₁ α .preserves =
      sym squarel
    Left .F-id =
      total-hom-path (Arrows C) (refl ,ₚ split-id _) prop!
    Left .F-∘ α β =
      total-hom-path (Arrows C) (refl ,ₚ split-∘ _ _ _) prop!

    -- Actually a vertical endofunctor on slices!
    Right : Functor (∫ (Arrows C)) (∫ (Arrows C))
    Right .F₀ ((x , y) , f) = (fac f , y) , right f
    Right .F₁ α .hom =
      split (α .hom .snd) (α .hom .fst) (sym (α .preserves)) ,
      α .hom .snd
    Right .F₁ α .preserves =
      sym squarer
    Right .F-id =
      total-hom-path (Arrows C) (split-id _ ,ₚ refl) prop!
    Right .F-∘ α β =
      total-hom-path (Arrows C) (split-∘ _ _ _ ,ₚ refl) prop!
```

```agda
    -- These are actually vertical natural transformations.
    counit : Left => Id
    counit .η ((x , y) , f) .hom = id , right f
    counit .η ((x , y) , f) .preserves = idr _ ∙ sym factors
    counit .is-natural _ _ _ =
      total-hom-path (Arrows C) (id-comm-sym ,ₚ sym squarer) prop!

    unit : Id => Right
    unit .η ((x , y) , f) .hom = left f , id
    unit .η ((x , y) , f) .preserves = factors ∙ sym (idl _)
    unit .is-natural _ _ _ =
      total-hom-path (Arrows C) (sym squarel ,ₚ id-comm-sym) prop!
```
