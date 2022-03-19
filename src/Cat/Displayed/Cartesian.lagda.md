```agda
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.Cartesian
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

open Precategory B
open Displayed E
```

# Cartesian Morphisms and Fibrations

```agda
record Cartesian {a b x y} (f : Hom a b)
                 (f′ : Hom[ f ] x y) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  field
    universal : ∀ {u u′} (m : Hom u a) → (h′ : Hom[ f ∘ m ] u′ y) → Hom[ m ] u′ x
    commutes  : ∀ {u u′} (m : Hom u a) → (h′ : Hom[ f ∘ m ] u′ y)
                → f′ ∘′ universal m h′ ≡ h′
    unique    : ∀ {u u′} {m : Hom u a} → {h′ : Hom[ f ∘ m ] u′ y}
                → (m′ : Hom[ m ] u′ x) → f′ ∘′ m′ ≡ h′ → m′ ≡ universal m h′
```

```agda
record Cartesian-lift {x y} (f : Hom x y) (y′ : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  field
    {x′}       : Ob[ x ]
    lifting   : Hom[ f ] x′ y′
    cartesian : Cartesian f lifting
```

```agda
record Cartesian-fibration : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  field
    has-lift : ∀ {x y} (f : Hom x y) → (y′ : Ob[ y ]) → Cartesian-lift f y′
```
