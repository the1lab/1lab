---
description: |
  We define the displayed category of elements.
---
<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Instances.Elements {o ℓ s} (B : Precategory o ℓ)
  (P : Functor (B ^op) (Sets s)) where
```

<!--
```agda
open Precategory B
open Functor

private
  module P = Functor P
```
-->

# The displayed category of elements

It is useful to view the [category of elements] of a presheaf
`P`{.Agda} as a [[displayed category]]. Instead of considering pairs of
objects $X$ and sections $s$, we instead think of the set of sections as
displayed _over_ $X$. The story is similar for morphisms; instead of
taking pairs of morphisms $f$ and fragments of data that $P(f)(x) = y$,
we place those fragments over the morphism $f$.

[category of elements]: Cat.Instances.Elements.html

In a sense, this is the more natural presentation of the category of
elements, as we obtain the more traditional definition by taking the
[[total category]] of `∫`{.Agda}.

```agda
∫ : Displayed B s s
∫ = with-thin-display record where
  Ob[_]            X = P ʻ X
  Hom[_] f P[X] P[Y] = P.₁ f P[Y] ≡ P[X]
  id' = happly P.F-id _
  _∘'_ {x = x} {y} {z} {f} {g} p q =
    P.₁ (f ∘ g) z   ≡⟨ happly (P.F-∘ g f) z ⟩
    P.₁ g (P.₁ f z) ≡⟨ ap (P.₁ g) p ⟩
    P.₁ g y         ≡⟨ q ⟩
    x               ∎
```
