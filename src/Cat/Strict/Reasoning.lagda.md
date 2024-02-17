```agda
open import Cat.Prelude

module Cat.Strict.Reasoning {o ℓ} (C : Precategory o ℓ) (ob-set : is-set ⌞ C ⌟) where

open Precategory C
```

# Reasoning with strict categories

When working with [[strict categories]], transports of morphisms along
paths between objects is (annoyingly) common; this module puts all of
the frustration in one place.

We provide shorthand operators for transporting morphisms.

```agda
cast-hom : ∀ {x x' y y' : Ob} → x ≡ x' → y ≡ y' → Hom x y → Hom x' y'
cast-hom p q f = transport (λ i → Hom (p i) (q i)) f

cast-cod : ∀ {x y y' : Ob} → y ≡ y' → Hom x y → Hom x y'
cast-cod p f = subst (λ y → Hom _ y) p f

cast-dom : ∀ {x x' y : Ob} → x ≡ x' → Hom x y → Hom x' y
cast-dom p f = subst (λ x → Hom x _) p f
```

We also characterize transports in identities and composites.

```agda
cast-id : ∀ {x x'} → (p : x ≡ x') → cast-hom p p id ≡ id
cast-id p = J (λ x p → cast-hom p p id ≡ id) (transport-refl id) p

cast-id-swap : ∀ {x x'} → (p : x ≡ x') → cast-cod p id ≡ cast-dom (sym p) id
cast-id-swap p = J (λ _ p → cast-cod p id ≡ cast-dom (sym p) id) refl p

cast-∘
  : ∀ {x x' y z z'} {f : Hom y z} {g : Hom x y}
  → (p : x ≡ x') (q : z ≡ z')
  → cast-hom p q (f ∘ g) ≡ cast-cod q f ∘ cast-dom p g
cast-∘ {f = f} {g = g} p q =
  J₂ (λ _ _ p q → cast-hom p q (f ∘ g) ≡ cast-cod q f ∘ cast-dom p g)
  (transport-refl _ ∙ sym (ap₂ _∘_ (transport-refl _) (transport-refl _)))
  p q

cast-cod-∘
  : ∀ {x y z z'} {f : Hom y z} {g : Hom x y}
  → (p : z ≡ z')
  → cast-cod p (f ∘ g) ≡ cast-cod p f ∘ g
cast-cod-∘ {f = f} {g = g} p =
  J (λ _ p → cast-cod p (f ∘ g) ≡ cast-cod p f ∘ g)
    (transport-refl _ ∙ ap (_∘ g) (sym (transport-refl _)))
    p

cast-dom-∘
  : ∀ {x x' y z} {f : Hom y z} {g : Hom x y}
  → (p : x ≡ x')
  → cast-dom p (f ∘ g) ≡ f ∘ cast-dom p g
cast-dom-∘ {f = f} {g = g} p =
  J (λ _ p → cast-dom p (f ∘ g) ≡ f ∘ cast-dom p g)
    (transport-refl _ ∙ ap (f ∘_) (sym (transport-refl _)))
    p
```

We also provide some lemmas for working with right/left identity laws that are
off by a cast.

```agda
cast-cod-idr : ∀ {x x' y : Ob} → (f : Hom x y) → (p : x' ≡ x)
        → f ∘ cast-cod p id ≡ cast-dom (sym p) f
cast-cod-idr {y = y} f p =
  J (λ x p → ∀ (f : Hom x y) → f ∘ cast-cod p id ≡ cast-dom (sym p) f)
    (λ f →  ap (f ∘_) (transport-refl _) ·· idr _ ·· sym (transport-refl _))
    p f

cast-dom-idl : ∀ {x y y' : Ob} → (f : Hom x y) → (p : y' ≡ y)
        → cast-dom p id ∘ f ≡ cast-cod (sym p) f
cast-dom-idl {x = x} f p =
  J (λ y p → ∀ (f : Hom x y) → cast-dom p id ∘ f ≡ cast-cod (sym p) f)
    (λ f → ap (_∘ f) (transport-refl _) ·· idl _ ·· sym (transport-refl _))
    p f
```

It doesn't matter what path you transport along, as $\cC$ is strict.

```agda
recast
  : ∀ {x x' y y'} {f : Hom x y}
  → (p p' : x ≡ x') (q q' : y ≡ y')
  → cast-hom p q f ≡ cast-hom p' q' f
recast {x} {x'} {y} {y'} {f} p p' q q' =
  transport
    (λ i → cast-hom (ob-set x x' p' p i) (ob-set y y' q' q i) f ≡ cast-hom p' q' f)
  refl

recast-dom
  : ∀ {x x' y} {f : Hom x y}
  → (p p' : x ≡ x')
  → cast-dom p f ≡ cast-dom p' f
recast-dom {x} {x'} {y'} {f} p p' =
  transport (λ i → cast-dom (ob-set x x' p' p i) f ≡ cast-dom p' f) refl

recast-cod
  : ∀ {x y y'} {f : Hom x y}
  → (p p' : y ≡ y')
  → cast-cod p f ≡ cast-cod p' f
recast-cod {x} {y} {y'} {f} p p' =
  transport (λ i → cast-cod (ob-set y y' p' p i) f ≡ cast-cod p' f) refl
```
