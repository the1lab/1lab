<!--
```agda
open import Cat.Displayed.Cartesian.Joint
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Product.Indexed
open import Cat.Displayed.Bifibration
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Trivial
  {o ℓ} (𝒞 : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Reasoning 𝒞
open Functor
open ∫Hom

private variable
  a b : Ob
  f g : Hom a b

private module ⊤Cat = Cat.Reasoning ⊤Cat
```
-->

# The trivial bifibration {defines="trivial-bifibration"}

Any category $\ca{C}$ can be regarded as being displayed over the
[[terminal category]] $\top$.

```agda
Trivial : Displayed ⊤Cat o ℓ
Trivial .Displayed.Ob[_] _ = Ob
Trivial .Displayed.Hom[_] _ = Hom
Trivial .Displayed.Hom[_]-set _ _ _ = Hom-set _ _
Trivial .Displayed.id' = id
Trivial .Displayed._∘'_ = _∘_
Trivial .Displayed.idr' = idr
Trivial .Displayed.idl' = idl
Trivial .Displayed.assoc' = assoc
```

<!--
```agda
module Trivial where
  open Cat.Displayed.Morphism Trivial public


trivial-invertible→invertible
  : ∀ {tt-inv : ⊤Cat.is-invertible tt}
  → Trivial.is-invertible[ tt-inv ] f
  → is-invertible f
trivial-invertible→invertible f-inv =
  make-invertible f.inv' f.invl' f.invr'
  where module f = Trivial.is-invertible[_] f-inv

invertible→trivial-invertible
  : ∀ {tt-inv : ⊤Cat.is-invertible tt}
  → is-invertible f
  → Trivial.is-invertible[ tt-inv ] f
invertible→trivial-invertible {tt-inv = tt-inv} f-inv =
  Trivial.make-invertible[ tt-inv ] f.inv f.invl f.invr
  where module f = is-invertible f-inv
```
-->

All morphisms in the trivial [[displayed category]] are vertical over
the same object, so producing cartesian lifts is extremely easy: just
use the identity morphism!

```agda
open Cocartesian-lift
open Cartesian-lift

Trivial-fibration : Cartesian-fibration Trivial
Trivial-fibration f y' .x' = y'
Trivial-fibration f y' .lifting = id
Trivial-fibration f y' .cartesian = cartesian-id Trivial
```

We can use a similar line of argument to deduce that it is also an opfibration.

```agda
Trivial-opfibration : Cocartesian-fibration Trivial
Trivial-opfibration f x' .y' =
  x'
Trivial-opfibration f x' .lifting = id
Trivial-opfibration f x' .cocartesian = cocartesian-id Trivial
```

Therefore, it is also a bifibration.

```agda
Trivial-bifibration : is-bifibration Trivial
Trivial-bifibration .is-bifibration.fibration = Trivial-fibration
Trivial-bifibration .is-bifibration.opfibration = Trivial-opfibration
```

The joint cartesian morphisms in the trivial displayed category
are precisely the projections out of [[indexed products]].

```agda
trivial-joint-cartesian→product
  : ∀ {κ} {Ix : Type κ}
  → {∏xᵢ : Ob} {xᵢ : Ix → Ob} {π : (i : Ix) → Hom ∏xᵢ (xᵢ i)}
  → is-jointly-cartesian Trivial (λ _ → tt) π
  → is-indexed-product 𝒞 xᵢ π

product→trivial-joint-cartesian
  : ∀ {κ} {Ix : Type κ}
  → {∏xᵢ : Ob} {xᵢ : Ix → Ob} {π : (i : Ix) → Hom ∏xᵢ (xᵢ i)}
  → is-indexed-product 𝒞 xᵢ π
  → is-jointly-cartesian Trivial (λ _ → tt) π
```

<details>
<summary>The proofs are basically just shuffling data around,
so we will not describe the details.
</summary>

```agda
trivial-joint-cartesian→product {xᵢ = xᵢ} {π = π} π-cart =
  π-product
  where
    module π = is-jointly-cartesian π-cart
    open is-indexed-product

    π-product : is-indexed-product 𝒞 xᵢ π
    π-product .tuple fᵢ = π.universal tt fᵢ
    π-product .commute = π.commutes tt _ _
    π-product .unique fᵢ p = π.unique _ p

product→trivial-joint-cartesian {xᵢ = xᵢ} {π = π} π-product =
  π-cart
  where
    module π = is-indexed-product π-product
    open is-jointly-cartesian

    π-cart : is-jointly-cartesian Trivial (λ _ → tt) π
    π-cart .universal tt fᵢ = π.tuple fᵢ
    π-cart .commutes tt fᵢ ix = π.commute
    π-cart .unique other p = π.unique _ p
```
</details>

In contrast, the cartesian morphisms in the trivial displayed category
are the invertible morphisms.

```agda
invertible→trivial-cartesian
  : ∀ {a b} {f : Hom a b}
  → is-invertible f
  → is-cartesian Trivial tt f

trivial-cartesian→invertible
  : ∀ {a b} {f : Hom a b}
  → is-cartesian Trivial tt f
  → is-invertible f
```

The forward direction is easy: every invertible morphism is cartesian,
and the invertible morphisms in the trivial displayed category on $\cC$ are
the invertible maps in $\cC$.

```agda
invertible→trivial-cartesian f-inv =
  invertible→cartesian Trivial
    (⊤Cat-is-pregroupoid tt)
    (invertible→trivial-invertible f-inv)
```

For the reverse direction, recall that all vertical cartesian morphisms
are invertible. Every morphism in the trivial displayed category is vertical,
so cartesianness implies invertibility.

```agda
trivial-cartesian→invertible f-cart =
  trivial-invertible→invertible $
  vertical+cartesian→invertible Trivial f-cart
```


Furthermore, the [[total category]] of the trivial bifibration is *isomorphic*
to the category we started with.

```agda
trivial-total : Functor (∫ Trivial) 𝒞
trivial-total .F₀ = snd
trivial-total .F₁ = snd
trivial-total .F-id = refl
trivial-total .F-∘ _ _ = refl

trivial-total-iso : is-precat-iso trivial-total
trivial-total-iso .is-precat-iso.has-is-ff = is-iso→is-equiv $ iso (∫hom tt)
  (λ _ → refl)
  (λ _ → ext refl)
trivial-total-iso .is-precat-iso.has-is-iso = is-iso→is-equiv $ iso (tt ,_)
  (λ _ → refl)
  (λ _ → refl ,ₚ refl)
```

As the trivial bifibration only has one fibre, this fibre is also
isomorphic to $\cE$.

```agda
trivial-fibre : Functor (Fibre Trivial tt) 𝒞
trivial-fibre .F₀ x = x
trivial-fibre .F₁ f = f
trivial-fibre .F-id = refl
trivial-fibre .F-∘ _ _ = transport-refl _

trivial→fibre-iso : is-precat-iso trivial-fibre
trivial→fibre-iso .is-precat-iso.has-is-ff = id-equiv
trivial→fibre-iso .is-precat-iso.has-is-iso = id-equiv
```
