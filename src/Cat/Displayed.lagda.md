```agda
{-# OPTIONS --type-in-type #-}
open import 1Lab.Prelude hiding (id; _∘_)
open import Category.Base

module Category.Displayed where
```

# Displayed Categories

```agda
record Displayed {o ℓ e } (B : Precategory o ℓ) (o′ ℓ′ : Level) : Type (o ⊔ ℓ ⊔ e ⊔ lsuc o′ ⊔ lsuc ℓ′) where
  open Precategory B

  field
    Ob[_] : Ob → Type o′
    Hom[_] : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ] → Type ℓ′
    Hom[_]-set : ∀ {a b} (f : Hom a b) → (x : Ob[ a ]) → (y : Ob[ b ]) → isSet (Hom[ f ] x y)
    id′ : ∀ {a} {x : Ob[ a ]} → Hom[ id ] x x
    _∘′_ : ∀ {a b c x y z} {f : Hom b c} {g : Hom a b} → Hom[ f ] y z → Hom[ g ] x y → Hom[ f ∘ g ] x z

  infixr 40 _∘′_

  _≡[_]_ : ∀ {a b x y} {f g : Hom a b} → Hom[ f ] x y → f ≡ g → Hom[ g ] x y → Type
  _≡[_]_ {a} {b} {x} {y} f′ p g′ = PathP (λ i → Hom[ p i ] x y) f′ g′

  infix 30 _≡[_]_

  field
    idr′ : ∀ {a b x y} {f : Hom a b} → (f′ : Hom[ f ] x y) → (f′ ∘′ id′) ≡[ idr f ] f′
    idl′ : ∀ {a b x y} {f : Hom a b} → (f′ : Hom[ f ] x y) → (id′ ∘′ f′) ≡[ idl f ] f′
    assoc′ : ∀ {a b c d w x y z} {f : Hom c d} {g : Hom b c} {h : Hom a b} →
               (f′ : Hom[ f ] y z) → (g′ : Hom[ g ] x y) → (h′ : Hom[ h ] w x) → f′ ∘′ (g′ ∘′ h′) ≡[ assoc f g h ] ((f′ ∘′ g′) ∘′ h′)
```
