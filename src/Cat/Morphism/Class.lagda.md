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

When defining [[factorisation systems|orthogonal-factorisation-system]]
and lifting properties, we need to consider collections of morphisms in
a category $\cC$. In theory, a class of morphisms is encoded into type
theory as a simple inhabitant of `∀ {x y} → Hom x y → Ω`. We however
prefer to have an explicit *record* type classifying these to aid with
formalisation. The reasons are twofold:

* Mikan's elaboration algorithm is fairly aggressive with inserting
  implicit arguments and binders. This can sometimes lead to situations
  where referring to a class of morphisms leaves metavariables to go
  unsolved if the specific relevant `Hom`{.Agda} is not definitionally
  injective in the objects.

* The bare function type only makes reference to the `Hom`{.Agda} field
  of the precategory $\cC$, and not to the overall object itself. This
  means that the category to which a class of arrows belongs to can not
  be inferred from the class of arrows itself, which generally means
  that it would have to be an additional explicit argument to any
  function parametrised over a class.

Passing around inhabitants of a record type prevents both of these
issues: the record makes reference to the entire precategory, so it is
definitionally injective, and it is not headed by an implicit function
space, so no implicit insertion takes place.

```agda
record Arrows {o ℓ} (C : Precategory o ℓ) (κ : Level) : Type (o ⊔ ℓ ⊔ lsuc κ) where
  no-eta-equality
  field
    arrows : ∀ {x y} → Precategory.Hom C x y → Type κ
    is-tr  : ∀ {x y} {f : Precategory.Hom C x y} → is-prop (arrows f)

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

<!--
```agda
module _ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd} where
  open Functor
```
-->

When $F : \cC \to \cD$ is a functor and $S \subseteq \cD$ is a class of morphisms,
then we can form a class of morphisms $F^{*}(S) \subseteq \cC$ spanned by all
morphisms of the form $f : \cC(x, y)$ such that $F(f) \in S$.

```agda
  F-restrict-arrows : ∀ {κ} → Functor C D → Arrows D κ → Arrows C κ
  F-restrict-arrows F S .arrows f = F .F₁ f ∈ S
  F-restrict-arrows F S .is-tr = S .is-tr
```
