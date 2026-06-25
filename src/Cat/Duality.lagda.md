<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Prelude

open Functor
```
-->
```agda
module Cat.Duality {o ℓ} {C : Precategory o ℓ} where
```

# Duality {defines="duality-of-precategories"}

Here we explore some features of duality in category theory, which is
intimately related to the [[opposite category]]. An important aspect of
this is the involutary nature of `_^op`{.Agda}, which we show here as an
[[isomorphism of precategories]] $(\cC\op)\op \cong \cC$.

```agda
^op^op→ : Functor (C ^op ^op) C
^op^op→ .F₀ x = x
^op^op→ .F₁ f = f
^op^op→ .F-id = refl
^op^op→ .F-∘ f g = refl

^op^op-is-iso : is-precat-iso ^op^op→
^op^op-is-iso = iso id-equiv id-equiv
```

This induces a [[path between precategories]]

```agda
C^op^op≡C : C ^op ^op ≡ C
C^op^op≡C = Precategory-path ^op^op→ ^op^op-is-iso
```

and an adjoint equivalence

```agda
^op^op-is-equiv : is-equivalence ^op^op→
^op^op-is-equiv = is-precat-iso→is-equivalence ^op^op-is-iso

^op^op← : Functor C (C ^op ^op)
^op^op← = is-equivalence.F⁻¹ ^op^op-is-equiv
```

Discussion of particular aspects of duality in category theory can be
found at:

- [Duality of morphisms]
- [Duality of hom functors]
- [Duality of product categories]
- [Duality of functor categories]
- [Duality of bifunctors]

[Duality of morphisms]: Cat.Morphism.Duality.html
[Duality of hom functors]: Cat.Functor.Hom.Duality.html
[Duality of product categories]: Cat.Instances.Product.Duality.html
[Duality of functor categories]: Cat.Instances.Functor.Duality.html
[Duality of bifunctors]: Cat.Functor.Bifunctor.Duality.html
