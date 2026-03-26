<!--
```agda
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Naturality where
```

# Working with natural transformations {defines="natural-isomorphism"}

Working with natural transformations can often be more cumbersome than
working directly with the underlying families of morphisms; moreover, we
often have to convert between a property of natural transformations and
a (universally quantified) property of the underlying morphisms. This
module collects some notation that will help us with that task.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  private
    module CD = Cat.Reasoning Cat[ C , D ]
    module D = Cat.Reasoning D
    module C = Cat.Reasoning C
  open Functor
  open _=>_
```
-->

We'll refer to the natural-transformation versions of predicates on
morphisms by a superscript `ⁿ`. A **natural isomorphism** is simply an
isomorphism in a functor category.

```agda
  Inversesⁿ : {F G : Functor C D} → F => G → G => F → Type _
  Inversesⁿ = CD.Inverses

  is-invertibleⁿ : {F G : Functor C D} → F => G → Type _
  is-invertibleⁿ = CD.is-invertible

  _≅ⁿ_ : Functor C D → Functor C D → Type _
  F ≅ⁿ G = CD.Isomorphism F G
```

<!--
```agda
  module Inversesⁿ {F G : Functor C D} {α : F => G} {β : G => F} (inv : Inversesⁿ α β) =
    CD.Inverses inv
  module is-invertibleⁿ {F G : Functor C D} {α : F => G} (inv : is-invertibleⁿ α) =
    CD.is-invertible inv
  module Isoⁿ {F G : Functor C D} (eta : F ≅ⁿ G) = CD._≅_ eta

  idni : ∀ {F} → F ≅ⁿ F
  idni = CD.id-iso

  _∘ni_ : ∀ {F G H} → G ≅ⁿ H → F ≅ⁿ G → F ≅ⁿ H
  _∘ni_ = CD._∘Iso_

  _∙ni_ : ∀ {F G H} → F ≅ⁿ G → G ≅ⁿ H → F ≅ⁿ H
  f ∙ni g = g ∘ni f

  _ni⁻¹ : ∀ {F G} → F ≅ⁿ G → G ≅ⁿ F
  _ni⁻¹ = CD._Iso⁻¹

  infixr 30 _∘ni_ _∙ni_
  infix 31 _ni⁻¹

  ≅ⁿ-pathp : ∀ {a c b d : Functor C D} (p : a ≡ c) (q : b ≡ d) {f : a ≅ⁿ b} {g : c ≅ⁿ d}
           → (∀ x → PathP (λ i → D.Hom (p i .F₀ x) (q i .F₀ x)) (Isoⁿ.to f .η x) (Isoⁿ.to g .η x))
           → PathP (λ i → p i CD.≅ q i) f g
  ≅ⁿ-pathp p q r = CD.≅-pathp p q (Nat-pathp p q r)
```
-->

A fundamental lemma that will let us work with natural isomorphisms more
conveniently is the following: if $\alpha : F \To G$ is a natural
transformation which is componentwise inverted by $\beta_{-} : G(-) \to
F(-)$, then $\beta$ is itself a natural transformation $G \To F$. This
means that, when constructing a natural isomorphism from scratch, we
only have to establish naturality in one direction, rather than both.

```agda
  inverse-is-natural
    : ∀ {F G : Functor C D} (α : F => G) (β : ∀ x → D.Hom (G .F₀ x) (F .F₀ x) )
    → (∀ x → α .η x D.∘ β x ≡ D.id)
    → (∀ x → β x D.∘ α .η x ≡ D.id)
    → is-natural-transformation G F β
  inverse-is-natural {F = F} {G = G} α β invl invr x y f =
    β y D.∘ G .F₁ f                    ≡⟨ D.refl⟩∘⟨ D.intror (invl x) ⟩
    β y D.∘ G .F₁ f D.∘ α .η x D.∘ β x ≡⟨ D.refl⟩∘⟨ D.extendl (sym (α .is-natural x y f)) ⟩
    β y D.∘ α .η y D.∘ F .F₁ f D.∘ β x ≡⟨ D.cancell (invr y) ⟩
    F .F₁ f D.∘ β x ∎
```

We can then create a natural isomorphism $F \cong^n G$ from the
following data:

```agda
  record make-natural-iso (F G : Functor C D) : Type (o ⊔ ℓ ⊔ ℓ') where
    no-eta-equality
    field
      eta : ∀ x → D.Hom (F .F₀ x) (G .F₀ x)
      inv : ∀ x → D.Hom (G .F₀ x) (F .F₀ x)
      eta∘inv : ∀ x → eta x D.∘ inv x ≡ D.id
      inv∘eta : ∀ x → inv x D.∘ eta x ≡ D.id
      natural : ∀ x y f → G .F₁ f D.∘ eta x ≡ eta y D.∘ F .F₁ f

  open make-natural-iso

  to-natural-iso : ∀ {F G} → make-natural-iso F G → F ≅ⁿ G
  {-# INLINE to-natural-iso #-}
  to-natural-iso {F = F} {G = G} mk =
    let to = record { η = mk .eta ; is-natural = λ x y f → sym (mk .natural x y f) } in
    record
      { to = to
      ; from = record
        { η = mk .inv
        ; is-natural = inverse-is-natural {F} {G} to (mk .inv) (mk .eta∘inv) (mk .inv∘eta) }
      ; inverses = record
        { invl = ext (mk .eta∘inv)
        ; invr = ext (mk .inv∘eta) } }
```

Moreover, the following family of functions project out the
componentwise invertibility, resp. componentwise isomorphism, associated
to an invertible natural transformation, resp. natural isomorphism.

```agda
  is-invertibleⁿ→is-invertible
    : ∀ {F G} {α : F => G}
    → is-invertibleⁿ α
    → ∀ x → D.is-invertible (α .η x)
  is-invertibleⁿ→is-invertible inv x =
    D.make-invertible
      (CD.is-invertible.inv inv .η x)
      (CD.is-invertible.invl inv ηₚ x)
      (CD.is-invertible.invr inv ηₚ x)

  isoⁿ→iso
    : ∀ {F G} → F ≅ⁿ G
    → ∀ x → F .F₀ x D.≅ G .F₀ x
  isoⁿ→iso α x =
    D.make-iso (α.to .η x) (α.from .η x) (α.invl ηₚ x) (α.invr ηₚ x)
    where module α = Isoⁿ α

  iso→isoⁿ
    : ∀ {F G}
    → (is : ∀ x → F .F₀ x D.≅ G .F₀ x)
    → (∀ {x y} f → G .F₁ f D.∘ is x .D.to ≡ is y .D.to D.∘ F .F₁ f)
    → F ≅ⁿ G
  {-# INLINE iso→isoⁿ #-}
  iso→isoⁿ {F} {G} is nat = to-natural-iso record where
    eta x = is x .D.to
    inv x = is x .D.from
    eta∘inv x = is x .D.invl
    inv∘eta x = is x .D.invr
    natural _ _ = nat

  is-invertibleⁿ→isoⁿ : ∀ {F G} {α : F => G} → is-invertibleⁿ α → F ≅ⁿ G
  is-invertibleⁿ→isoⁿ nat-inv = CD.invertible→iso _ nat-inv

  isoⁿ→is-invertible
    : ∀ {F G} (α : F ≅ⁿ G)
    → ∀ x → D.is-invertible (α .Isoⁿ.to .η x)
  isoⁿ→is-invertible α x = D.iso→invertible (isoⁿ→iso α x)
```

<!--
```agda
  to-inversesⁿ
    : {F G : Functor C D} {α : F => G} {β : G => F}
    → (∀ x → α .η x D.∘ β .η x ≡ D.id)
    → (∀ x → β .η x D.∘ α .η x ≡ D.id)
    → Inversesⁿ α β
  to-inversesⁿ p q = CD.make-inverses (ext p) (ext q)

  to-is-invertibleⁿ
    : {F G : Functor C D} {α : F => G}
    → (β : G => F)
    → (∀ x → α .η x D.∘ β .η x ≡ D.id)
    → (∀ x → β .η x D.∘ α .η x ≡ D.id)
    → is-invertibleⁿ α
  to-is-invertibleⁿ β p q = CD.make-invertible β (ext p) (ext q)

  inversesⁿ→inverses
    : ∀ {F G} {α : F => G} {β : G => F}
    → Inversesⁿ α β
    → ∀ x → D.Inverses (α .η x) (β .η x)
  inversesⁿ→inverses inv x =
    D.make-inverses
      (CD.Inverses.invl inv ηₚ x)
      (CD.Inverses.invr inv ηₚ x)

  isoⁿ→is-invertibleⁿ : ∀ {F G : Functor C D} (i : F ≅ⁿ G) → is-invertibleⁿ (Isoⁿ.to i)
  isoⁿ→is-invertibleⁿ i = CD.iso→invertible i

  invertible→invertibleⁿ
    : ∀ {F G} (eta : F => G)
    → (∀ x → D.is-invertible (eta .η x))
    → is-invertibleⁿ eta
  invertible→invertibleⁿ eta i = to-is-invertibleⁿ ate (λ x → D.is-invertible.invl (i x)) λ x → D.is-invertible.invr (i x) where
    ate : _ => _
    ate .η x = D.is-invertible.inv (i x)
    ate .is-natural = inverse-is-natural eta _ (λ x → D.is-invertible.invl (i x)) (λ x → D.is-invertible.invr (i x))

  push-eqⁿ : ∀ {F G} (α : F ≅ⁿ G) {a b} {f g : C.Hom a b} → F .F₁ f ≡ F .F₁ g → G .F₁ f ≡ G .F₁ g
  push-eqⁿ {F = F} {G = G} α {f = f} {g} p =
    G .F₁ f                                           ≡⟨ D.insertl (α .Isoⁿ.invl ηₚ _) ⟩
    α .Isoⁿ.to .η _ D.∘ α .Isoⁿ.from .η _ D.∘ G .F₁ f ≡⟨ D.refl⟩∘⟨ α .Isoⁿ.from .is-natural _ _ _ ⟩
    α .Isoⁿ.to .η _ D.∘ F .F₁ f D.∘ α .Isoⁿ.from .η _ ≡⟨ D.refl⟩∘⟨ p D.⟩∘⟨refl ⟩
    α .Isoⁿ.to .η _ D.∘ F .F₁ g D.∘ α .Isoⁿ.from .η _ ≡˘⟨ D.refl⟩∘⟨ α .Isoⁿ.from .is-natural _ _ _ ⟩
    α .Isoⁿ.to .η _ D.∘ α .Isoⁿ.from .η _ D.∘ G .F₁ g ≡⟨ D.cancell (α .Isoⁿ.invl ηₚ _) ⟩
    G .F₁ g                                           ∎
```
-->


<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    open _=>_

  id-nat-commute : ∀ (α β : Id {C = C} => Id) → α ∘nt β ≡ β ∘nt α
  id-nat-commute α β = ext λ x → α .is-natural _ _ _
```
-->
