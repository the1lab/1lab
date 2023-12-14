<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Shape.Terminal
open import Cat.Displayed.Bifibration
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Instances.Trivial
  {o ℓ} (𝒞 : Precategory o ℓ)
  where
```

<!--
```
open Precategory 𝒞
open Functor
open Total-hom
```
-->

# The trivial bifibration

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

All morphisms in the trivial [[displayed category]] are vertical over
the same object, so producing cartesian lifts is extremely easy: just
use the identity morphism!

```agda
open Cartesian-fibration
open Cocartesian-fibration
open Cartesian-lift
open Cocartesian-lift

Trivial-fibration : Cartesian-fibration Trivial
Trivial-fibration .has-lift f y' .x' = y'
Trivial-fibration .has-lift f y' .lifting = id
Trivial-fibration .has-lift f y' .cartesian = cartesian-id Trivial
```

We can use a similar line of argument to deduce that it is also an opfibration.

```agda
Trivial-opfibration : Cocartesian-fibration Trivial
Trivial-opfibration .has-lift f x' .y' =
  x'
Trivial-opfibration .has-lift f x' .lifting = id
Trivial-opfibration .has-lift f x' .cocartesian = cocartesian-id Trivial
```

Therefore, it is also a bifibration.

```agda
Trivial-bifibration : is-bifibration Trivial
Trivial-bifibration .is-bifibration.fibration = Trivial-fibration
Trivial-bifibration .is-bifibration.opfibration = Trivial-opfibration
```

Furthermore, the [[total category]] of the trivial bifibration is *isomorphic*
to the category we started with.

```agda
trivial-total : Functor (∫ Trivial) 𝒞
trivial-total .F₀ = snd
trivial-total .F₁ = preserves
trivial-total .F-id = refl
trivial-total .F-∘ _ _ = refl

trivial-total-iso : is-precat-iso trivial-total
trivial-total-iso .is-precat-iso.has-is-ff =
  is-iso→is-equiv $
    iso (total-hom tt)
        (λ _ → refl)
        (λ _ → total-hom-pathp Trivial refl refl refl refl)
trivial-total-iso .is-precat-iso.has-is-iso =
  is-iso→is-equiv $
    iso (tt ,_)
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
