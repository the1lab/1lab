<!--
```agda
open import Cat.Displayed.Bifibration
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Chaotic
  {o ℓ o' ℓ'} (B : Precategory o ℓ) (J : Precategory o' ℓ')
  where

private
  module B = Cat.Reasoning B
  module J = Cat.Reasoning J

open Functor
open Displayed
open Total-hom
```

# The chaotic bifibration

Let $\cB$ and $\cJ$ be precategories. We define the
**chaotic bifibration** of $\cJ$ over $\cB$ to be the [[displayed
category]] where we trivially fibre $\cJ$ over $\cB$, disregarding the
structure of $\cB$ entirely.

```agda
Chaotic : Displayed B o' ℓ'
Chaotic. Ob[_] _ = J.Ob
Chaotic .Hom[_] _ = J.Hom
Chaotic .Hom[_]-set _ = J.Hom-set
Chaotic .id' = J.id
Chaotic ._∘'_ = J._∘_
Chaotic .idr' = J.idr
Chaotic .idl' = J.idl
Chaotic .assoc' = J.assoc
```

Note that the only [[cartesian morphisms]] in the chaotic bifibration are
the isomorphisms in $\cJ$:

```agda
chaotic-cartesian→is-iso
  : ∀ {x y x' y'} {f : B.Hom x y} {g : J.Hom x' y'}
  → is-cartesian Chaotic f g → J.is-invertible g
chaotic-cartesian→is-iso cart =
  J.make-invertible
    (universal B.id J.id)
    (commutes B.id J.id)
    (unique _ (J.cancell (commutes B.id J.id))
     ∙ sym (unique {m = B.id} J.id (J.idr _)))
  where open is-cartesian cart

is-iso→chaotic-cartesian
  : ∀ {x y x' y'} {f : B.Hom x y} {g : J.Hom x' y'}
  → J.is-invertible g → is-cartesian Chaotic f g
is-iso→chaotic-cartesian {f = f} {g = g} is-inv = cart
  where
    open J.is-invertible is-inv
    open is-cartesian

    cart : is-cartesian Chaotic f g
    cart .universal _ h = inv J.∘ h
    cart .commutes _ h = J.cancell invl
    cart .unique {h' = h} m p =
      m                     ≡⟨ J.introl invr ⟩
      (inv J.∘ g) J.∘ m     ≡⟨ J.pullr p ⟩
      inv J.∘ h             ∎
```

This implies that the chaotic fibration is a fibration, as $id$ is
invertible, and also lies above every morphism in $\cB$. We could
use our lemmas from before to show this, but doing it by hand lets
us avoid an extra `id` composite when constructing the universal map.

```agda
Chaotic-fibration : Cartesian-fibration Chaotic
Chaotic-fibration .Cartesian-fibration.has-lift f y = cart-lift where
  open Cartesian-lift
  open is-cartesian

  cart-lift : Cartesian-lift Chaotic f y
  cart-lift .x' = y
  cart-lift .lifting = J.id
  cart-lift .cartesian .universal _ g = g
  cart-lift .cartesian .commutes _ g = J.idl g
  cart-lift .cartesian .unique m p = sym (J.idl m) ∙ p
```

We observe a similar situation for cocartesian morphisms.

```agda
chaotic-cocartesian→is-iso
  : ∀ {x y x' y'} {f : B.Hom x y} {g : J.Hom x' y'}
  → is-cocartesian Chaotic f g → J.is-invertible g
chaotic-cocartesian→is-iso cocart =
  J.make-invertible
    (universal B.id J.id)
    (unique _ (J.cancelr (commutes B.id J.id))
     ∙ sym (unique {m = B.id} J.id (J.idl _)))
    (commutes B.id J.id)
  where open is-cocartesian cocart

is-iso→chaotic-cocartesian
  : ∀ {x y x' y'} {f : B.Hom x y} {g : J.Hom x' y'}
  → J.is-invertible g → is-cocartesian Chaotic f g
is-iso→chaotic-cocartesian {f = f} {g = g} is-inv = cocart
  where
    open J.is-invertible is-inv
    open is-cocartesian

    cocart : is-cocartesian Chaotic f g
    cocart .universal _ h = h J.∘ inv
    cocart .commutes _ h = J.cancelr invr
    cocart .unique {h' = h} m p =
      m               ≡⟨ J.intror invl ⟩
      m J.∘ g J.∘ inv ≡⟨ J.pulll p ⟩
      h J.∘ inv       ∎

Chaotic-opfibration : Cocartesian-fibration Chaotic
Chaotic-opfibration .Cocartesian-fibration.has-lift f x' = cocart-lift where
  open Cocartesian-lift
  open is-cocartesian

  cocart-lift : Cocartesian-lift Chaotic f x'
  cocart-lift .y' = x'
  cocart-lift .lifting = J.id
  cocart-lift .cocartesian .universal _ g = g
  cocart-lift .cocartesian .commutes _ g = J.idr g
  cocart-lift .cocartesian .unique m p = sym (J.idr m) ∙ p
```

This implies that the chaotic bifibration actually lives up to its name.

```agda
Chaotic-bifibration : is-bifibration Chaotic
Chaotic-bifibration .is-bifibration.fibration = Chaotic-fibration
Chaotic-bifibration .is-bifibration.opfibration = Chaotic-opfibration
```

## Fibre categories

Unsurprisingly, the [[fibre categories]] of the chaotic bifibration are
isomorphic to $\cJ$.

```agda
ChaoticFib : ∀ x → Functor J (Fibre Chaotic x)
ChaoticFib x .F₀ j = j
ChaoticFib x .F₁ f = f
ChaoticFib x .F-id = refl
ChaoticFib x .F-∘ _ _ = sym (transport-refl _)

ChaoticFib-is-iso : ∀ x → is-precat-iso (ChaoticFib x)
ChaoticFib-is-iso x .is-precat-iso.has-is-ff = id-equiv
ChaoticFib-is-iso x .is-precat-iso.has-is-iso = id-equiv
```

## Total category

The [[total category]] of the chaotic bifibration is isomorphic to the
product of $\cB$ and $\cJ$.

```agda
ChaoticTotal : Functor (B ×ᶜ J) (∫ Chaotic)
ChaoticTotal .F₀ bj = bj
ChaoticTotal .F₁ (f , g) = total-hom f g
ChaoticTotal .F-id = total-hom-path Chaotic refl refl
ChaoticTotal .F-∘ f g = total-hom-path Chaotic refl refl

ChaoticTotal-is-iso : is-precat-iso ChaoticTotal
ChaoticTotal-is-iso .is-precat-iso.has-is-ff =
  is-iso→is-equiv
    (iso (λ f → f .hom , f .preserves)
    (λ _ → total-hom-path Chaotic refl refl)
    (λ _ → refl))
ChaoticTotal-is-iso .is-precat-iso.has-is-iso = id-equiv
```
