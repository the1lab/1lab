<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Product.Duality {o₁ h₁ o₂ h₂ : Level}
  {C : Precategory o₁ h₁} {D : Precategory o₂ h₂}
  where
```

<!--
```agda
open Precategory
open Functor
open _=>_
```
-->

# Duality of product categories {defines="opposite-product-category"}

As one might expect, taking the [[opposite category]] of a [[product category]]
agrees with the product of opposite categories. Rather than showing
equality we construct an [[isomorphism of precategories]].

```agda
×^op→ : Functor ((C ×ᶜ D)^op) (C ^op ×ᶜ D ^op)
×^op→ .F₀ x = x
×^op→ .F₁ f = f
×^op→ .F-id = refl
×^op→ .F-∘ f g = refl

×^op-is-iso : is-precat-iso ×^op→
×^op-is-iso = iso has-is-ff has-is-iso where
  has-is-ff : Cat.Functor.Properties.is-fully-faithful ×^op→
  has-is-ff = id-equiv

  has-is-iso : is-equiv (F₀ ×^op→)
  has-is-iso = id-equiv
```

This means, in particular, that it is an adjoint equivalence:

```agda
×^op-is-equiv : is-equivalence ×^op→
×^op-is-equiv = is-precat-iso→is-equivalence ×^op-is-iso
```

The inverse can be given explicitly as below, by the exact same formula.

```agda
×^op← : Functor (C ^op ×ᶜ D ^op) ((C ×ᶜ D)^op)
×^op← .F₀ x = x
×^op← .F₁ f = f
×^op← .F-id = refl
×^op← .F-∘ f g = refl

private
  ×^op←-is-inverse : ×^op← ≡ is-equivalence.F⁻¹ ×^op-is-equiv
  ×^op←-is-inverse = Functor-path
    (λ _ → refl)
    (λ f → sym $ Regularity.reduce! ∙ (C.idr _ ∙ C.idl _ ,ₚ D.idr _ ∙ D.idl _))
    where
      module C = Precategory C
      module D = Precategory D
```

