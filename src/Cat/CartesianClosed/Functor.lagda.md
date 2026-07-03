<!--
```agda
open import Cat.Diagram.Exponential
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Functor.Reasoning
```
-->

```agda
module Cat.CartesianClosed.Functor where
```

# Cartesian closed functors {defines="cartesian-closed-functor exponential-comparison-map"}

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (F : Functor C D) {ccart : Cartesian-category C} {dcart : Cartesian-category D}
    (ccc : Cartesian-closed C ccart) (dcc : Cartesian-closed D dcart)
  where

  private
    module F = Cat.Functor.Reasoning F
    module C where
      open Cartesian-category ccart public
      open Cartesian-closed ccc public
    module D where
      open Cartesian-category dcart public
      open Cartesian-closed dcc public
```
-->

Let $F : \cC \to \cD$ be a [[Cartesian functor]] between [[cartesian
closed categories]]. Being Cartesian, $F$ relates the products of $\cC$
and $\cD$ up to isomorphism, so we may ask how it relates their
[[exponential objects]], too. Writing $\mu\inv$ for the inverse of the
[[product comparison map]], we can define an **exponential comparison**
map as the mate

$$
F(B^A) \xto{\lambda\left(F(\rm{ev}) \circ \mu\inv\right)} F(B)^{F(A)}
$$

of the image under $F$ of the evaluation map.

```agda
  module _ (cart : Cartesian-functor F ccart dcart) where
    open Cartesian-functor cart

    exp-comparison : ∀ A B → D.Hom (F.₀ C.[ A , B ]) D.[ F.₀ A , F.₀ B ]
    exp-comparison A B = D.ƛ (F.₁ C.ev D.∘ comparison.inv)
```

We say that a Cartesian functor **preserves exponentials** if its
exponential comparison map is invertible: the image of $B^A$ then
satisfies the universal property of $F(B)^{F(A)}$. A **cartesian closed
functor** is a Cartesian functor that preserves exponentials.

```agda
  record Cartesian-closed-functor : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      cartesian : Cartesian-functor F ccart dcart
      pres-exponentials
        : ∀ A B → D.is-invertible (exp-comparison cartesian A B)
```

This is the preservation notion that makes the interpretation of the
[[simply-typed lambda calculus|STLC]] stable under change of semantic
universe: composing a model with a cartesian closed functor is again a
model, with the same underlying syntax.
