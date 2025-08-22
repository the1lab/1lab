---
description: |
  Classes of morphisms.
---
<!--
```agda
open import 1Lab.Reflection
open import 1Lab.Prelude hiding (_∘_ ; id ; _↪_ ; _↠_)

open import Cat.Base
```
-->
```agda
module Cat.Morphism.Class where
```


# Classes of morphisms

When defining [[factorisation systems|orthogonal-factorisation-system]] and
lifting properties, we need to consider collections of morphisms in a category
$\cC$. Such collections can be naively encoded in Agda as a function
`∀ {x y} → Hom x y → Ω`, but this representation is somewhat suboptimal.
Agda is quite aggressive about automatically instantiating implicit
arguments, so passing around functions like `∀ {x y} → Hom x y → Ω`
as first-class objects can often lead to unsolved metavariable errors.

To work around this, we define a class of morphisms in a category $\cC$
as a single-field record type. This avoids the implicit instantiating
issue from before, at the cost of a bit of code bloat.

```agda
record Arrows {o ℓ} (C : Precategory o ℓ) (κ : Level) : Type (o ⊔ ℓ ⊔ lsuc κ) where
  no-eta-equality
  field
    arrows : ∀ {x y} → Precategory.Hom C x y → Type κ
    is-tr : ∀  {x y} {f : Precategory.Hom C x y} → is-prop (arrows f)

open Arrows public
```

<!--
```agda
{-# INLINE Arrows.constructor #-}

instance
  open hlevel-projection

  Arrows-hlevel-proj : hlevel-projection (quote Arrows.arrows)
  Arrows-hlevel-proj .has-level = quote Arrows.is-tr
  Arrows-hlevel-proj .get-level _ = pure (lit (nat 1))
  Arrows-hlevel-proj .get-argument (_ ∷ _ ∷ _ ∷ _ ∷ arg _ h ∷ _) = pure h
  {-# CATCHALL #-}
  Arrows-hlevel-proj .get-argument _ = typeError []


{-# DISPLAY Arrows.arrows S f = f ∈ S #-}

module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C

  instance
    Membership-Arrows : ∀ {κ} {x y} → Membership (Hom x y) (Arrows C κ) κ
    Membership-Arrows = record { _∈_ = λ f S → Arrows.arrows S f }

    Inclusion-Arrows : ∀ {κ} → Inclusion (Arrows C κ) (o ⊔ ℓ ⊔ κ)
    Inclusion-Arrows = record { _⊆_ = λ S T → ∀ {x y} → (f : Hom x y) → f ∈ S → f ∈ T }

    Funlike-Arrows : ∀ {κ} {x y} → Funlike (Arrows C κ) (Hom x y) λ _ → Prop κ
    Funlike-Arrows = record { _·_ = λ S f → el (S .arrows f) (S .is-tr) }

  private
    unquoteDecl arrows-iso = declare-record-iso arrows-iso (quote Arrows)

  Arrows≃ : ∀ {κ} → Arrows C κ ≃ (∀ {x y} → Hom x y → Prop κ)
  Arrows≃ .fst S f = el! (f ∈ S)
  Arrows≃ .snd = is-iso→is-equiv λ where
    .is-iso.from S → record { arrows = λ f → f ∈ S ; is-tr = hlevel 1 }
    .is-iso.rinv S → ext (λ x → n-path refl)
    .is-iso.linv S → Iso.injective arrows-iso (refl ,ₚ prop!)

  instance
    Extensional-Arrows
      : ∀ {κ ℓr} ⦃ _ : Extensional (∀ {x y} → Hom x y → Type κ) ℓr ⦄
      → Extensional (Arrows C κ) ℓr
    Extensional-Arrows {κ = κ} ⦃ e ⦄ = embedding→extensional (arrows , emb) e where abstract
      emb : is-embedding (Arrows.arrows {C = C} {κ = κ})
      emb = ∘-is-embedding {f = λ f g → g ∈ f} {g = Arrows≃ .fst}
        (cancellable→embedding
          ( (λ h → ext λ f → n-path λ i → h i f)
          , is-iso→is-equiv (iso (λ x i g → ⌞ x i g ⌟)
              (λ p i j f → n-Type-square {p = refl} {n-path (λ i → ⌞ p i f ⌟)} {λ i → p i f} {refl} refl i j)
              λ h → refl)
          ))
        (is-equiv→is-embedding (Arrows≃ .snd))
```
-->


We can take intersections of morphism classes.

```agda
  _∩ₐ_ : ∀ {κ κ'} → Arrows C κ → Arrows C κ' → Arrows C (κ ⊔ κ')
  (S ∩ₐ T) .arrows f = f ∈ S × f ∈ T
  (S ∩ₐ T) .is-tr = hlevel 1
```
