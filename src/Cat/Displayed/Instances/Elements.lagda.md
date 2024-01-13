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
Displayed.Ob[ ∫ ] X = ∣ P.₀ X ∣
Displayed.Hom[ ∫ ] f P[X] P[Y] = P.₁ f P[Y] ≡ P[X]
Displayed.Hom[ ∫ ]-set _ _ _ = hlevel!
∫ .Displayed.id' = happly P.F-id _
∫ .Displayed._∘'_ {x = x} {y = y} {z = z} {f = f} {g = g} p q = pf where abstract
  pf : P.₁ (f ∘ g) z ≡ x
  pf =
    P.₁ (f ∘ g) z   ≡⟨ happly (P.F-∘ g f) z ⟩
    P.₁ g (P.₁ f z) ≡⟨ ap (P.₁ g) p ⟩
    P.₁ g y         ≡⟨ q ⟩
    x               ∎
∫ .Displayed.idr' _ = to-pathp (P.₀ _ .is-tr _ _ _ _)
∫ .Displayed.idl' _ = to-pathp (P.₀ _ .is-tr _ _ _ _)
∫ .Displayed.assoc' _ _ _ = to-pathp (P.₀ _ .is-tr _ _ _ _)
```
