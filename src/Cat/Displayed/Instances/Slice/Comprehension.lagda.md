<!--
```agda
open import Cat.Displayed.Comprehension.Coproduct.VeryStrong
open import Cat.Displayed.Comprehension.Coproduct.Strong
open import Cat.Displayed.Comprehension.Coproduct
open import Cat.Diagram.Pullback.Properties
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Diagram.Pullback
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR

open has-comprehension-coproducts
open Comprehension-structure
open /-Obj
```
-->

```agda
module Cat.Displayed.Instances.Slice.Comprehension
  {o ℓ} (B : Precategory o ℓ)
  where
```

# The canonical comprehension category {defines="canonical-comprehension-category"}

The identity [[fibred functor]] of the [[canonical self-indexing]] of
any category $\cB$ is the prototypical example of a [[comprehension
category]].

```agda
  Slices-comprehension : Comprehension-structure (Slices B)
  Slices-comprehension .Comprehend = Id'
  Slices-comprehension .Comprehend-is-fibred = Id'-fibred
```

Assuming that $\cB$ has pullbacks (so that we can talk about its
[[codomain *fibration*]]), the canonical comprehension category has
[[comprehension coproducts]] given by its cocartesian lifts, which are
in turn given by composition.

<!--
```agda
  module _ (pullbacks : has-pullbacks B) where
    private
      fib = Codomain-fibration B pullbacks
      opfib = Codomain-opfibration B

    open CR B
    open Displayed (Slices B)
    open Cocartesian-fibration (Slices B) opfib
    open Comprehension (Slices B) fib Slices-comprehension

    opaque
      unfolding _⨾_
```
-->

```agda
      Slices-comprehension-coproducts
        : has-comprehension-coproducts fib fib Slices-comprehension
      Slices-comprehension-coproducts = record where
        ∐              x y = x .map ^! y
        ⟨_,_⟩          x y = ι! _ y
        ⟨⟩-cocartesian x y = ι!.cocartesian
        ∐-beck-chevalley cart = Slices-beck-chevalley B
          (rotate-pullback (cartesian→pullback B cart))
```

These comprehension coproducts are [[very strong|very strong
comprehension coproduct]] by construction: they model $\Sigma$-types.
This is one of those proofs whose name is longer than its definition,
since $\Gamma. X. Y$ and $\Gamma. \coprod_X Y$ are both interpreted as
the domain of the same map, and the canonical substitution between them
is just the identity.

```agda
      Slices-very-strong-comprehension-coproducts
        : very-strong-comprehension-coproducts
            Slices-comprehension Slices-comprehension-coproducts
      Slices-very-strong-comprehension-coproducts x y = id-invertible
```
