<!--
```agda
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Slice
open import Cat.Instances.Sets.Complete
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Terminal
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Hom as Hom
```
-->

```agda
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

Given a category $\cB$, we can construct a [[displayed category]] of
"Sierpinski cones" over $\cB$, or "scones" for short.  Scones provide a
powerful set of tools for proving various properties of categories that
we want to think of as somehow "syntactic".

A scone over some object $X : \cB$ consists of a set $U$, along with
a function $U \to B(\top, X)$. If we think about $\cB$ as some sort
of category of contexts, then a scone over some context $X$
is some means of attaching semantic information (the set $U$) to
$X$, such that we can recover closed terms of $X$ from elements of $U$.

Morphisms behave like they do in an arrow category of $\ca{Sets}$:
given a map $f : X \to Y$ in $\cB$, a map over $f$ in the category
between $(U, su : U \to \cB(1, X))$ and $(V, sv : V \to \cB(1, Y))$
consists of a function $uv : U \to V$, such that for all $u : U$,
we have $f \circ su(u) = sv (uv u)$.

~~~{.quiver}
\[\begin{tikzcd}
  U && V \\
  \\
  {\mathcal{B}(1, X)} && {\mathcal{B}(1, Y)}
  \arrow["uv", from=1-1, to=1-3]
  \arrow["su"', from=1-1, to=3-1]
  \arrow["sv"', from=1-3, to=3-3]
  \arrow["{f \circ-}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~


With the exposition out of the way, we can now define the category of
scones by abstract nonsense: the category of scones over $\cB$ is the
[[pullback|pullback fibration]] of the [[fundamental fibration]] along the
global sections functor.

~~~{.quiver}
\[\begin{tikzcd}
  {\mathrm{Scn}(\mathcal{B})} && {\mathrm{Arr}(\mathbf{Sets})} \\
  \\
  {\mathcal{B}} && {\mathbf{Sets}}
  \arrow["{\mathrm{Slices}(\mathbf{Sets})}", from=1-3, to=3-3]
  \arrow["{\mathcal{B}(1,-)}"', from=3-1, to=3-3]
  \arrow[lies over, dashed, from=1-1, to=3-1]
  \arrow[lies over, from=1-1, to=1-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
Scones : Displayed B (lsuc ℓ) ℓ
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

The category of scones over $\cB$ is always a fibration. This is
where our definition by abstract nonsense begins to shine: base change
preserves fibrations, and the codomain fibration is a fibration whenever
the base category has pullbacks, which sets [has]!

[has]: Cat.Instances.Sets.Complete.html#finite-set-limits

```agda
Scones-fibration : Cartesian-fibration Scones
Scones-fibration =
  Change-of-base-fibration _ _ $
  Codomain-fibration _ $
  Sets-pullbacks
```
