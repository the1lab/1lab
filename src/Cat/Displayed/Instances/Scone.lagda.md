```agda
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Slice
open import Cat.Instances.Sets.Complete
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Functor.Hom as Hom

module Cat.Displayed.Instances.Scone
  {o ℓ} (B : Precategory o ℓ)
  (terminal : Terminal B)
  where

open Precategory B
open Terminal terminal
open Hom B
open /-Obj
```

## Sierpinski cones

Given a category $\ca{B}$, we can construct a displayed category
of "Sierpinski Cones" over $\ca{B}$, or "Scones" for short.
Scones provide a powerful set of tools for proving various properties
of categories that we want to think of as somehow "syntactic".

A scone over some object $X : \ca{B}$ consists of a set $U$, along with
a function $U \to B(\top, X)$. If we think about $\ca{B}$ as some sort
of category of contexts, then a scone over some context $X$
is some means of attatching semantic information (the set $U$) to
$X$, such that we can recover closed terms of $X$ from elements of $U$.

Morphisms behave like they do in the slice category of $\ca{B}$:
given a map $f : X \to Y$ in $\ca{B}$, a map over $f$ in the category
between $(U, su : U \to \ca{B}(1, X))$ and $(V, sv : V \to \ca{B}(1, Y))$
consists of a function $uv : U \to V$, such that for all $u : U$,
we have $f \circ su(u) = sv (uv u)$.

We can make the exposition out of the way, we can now define the
category of scones. We do this by abstract nonsense, by performing
a base change along the global sections functor of the slice category
of $\ca{B}$.

```agda
Scones : Displayed B (lsuc ℓ) (lsuc ℓ)
Scones = Change-of-base Hom[ top ,-] (Slices (Sets ℓ))
```

We can unfold the abstract definition to see that we obtain the same
objects and morphisms described above.

<!--
```agda
private
  module Scones = Displayed Scones
  
```
-->

```agda
scone : ∀ {X} → (U : Set ℓ) → (∣ U ∣ → Hom top X) → Scones.Ob[ X ]
scone U s = cut {domain = U} s

scone-hom : ∀ {X Y} {f : Hom X Y} {U V : Set ℓ}
            → {su : ∣ U ∣ → Hom top X} {sv : ∣ V ∣ → Hom top Y}
            → (uv : ∣ U ∣ → ∣ V ∣)
            → (∀ u → f ∘ (su u) ≡ sv (uv u))
            → Scones.Hom[ f ] (scone U su) (scone V sv)
scone-hom uv p = slice-hom uv (funext p)
```

## As a fibration

The category of scones over $\ca{B}$ is always a fibration. This is
where our definition by abstract nonsense begins to shine: base change
preserves fibrations, and the codomain fibration is a fibration whenever
the base category has pullbacks, which sets has!

```agda
Scones-fibration : Cartesian-fibration Scones
Scones-fibration =
  Change-of-base-fibration _ _ $
  Codomain-fibration _ $
  Sets-pullbacks
```
