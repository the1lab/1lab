<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Product.Duality {o₁ h₁ o₂ h₂ : Level} 
  {C : Precategory o₁ h₁} {D : Precategory o₁ h₁}
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
×^op-is-iso = iso id-equiv id-equiv
```

This induces a [[path between precategories]]

```agda
×^op-path : (C ×ᶜ D)^op ≡ C ^op ×ᶜ D ^op
×^op-path = Precategory-path ×^op→ ×^op-is-iso
```

and an adjoint equivalence

```agda
×^op-is-equiv : is-equivalence ×^op→
×^op-is-equiv = is-precat-iso→is-equivalence ×^op-is-iso

×^op← : Functor (C ^op ×ᶜ D ^op) ((C ×ᶜ D)^op)
×^op← = is-equivalence.F⁻¹ ×^op-is-equiv
```
