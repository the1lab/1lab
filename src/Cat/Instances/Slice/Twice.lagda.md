<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Slice.Twice {o ℓ} {C : Precategory o ℓ} where
```

<!--
```agda
open Cat.Reasoning C
open Functor
open /-Obj
open /-Hom
open _=>_
open _⊣_
private variable
  a b : Ob
```
-->

# Iterated slice categories {defines="iterated-slice"}

An **iterated slice category**, something like $(\cC/B)/f$ for $f : A
\to B$ (regarded as an object over $B$), is something slightly
mind-bending to consider at face value: the objects are _families of
families-over-$B$_, indexed by the family $f$? It sounds like there's a
lot of room for complexity here, and that's only considering one
iteration!

Fortunately, there's actually _no such thing_. The slice of $\cC/B$ over
$f$ is isomorphic to the slice $\cC/A$, by a functor which is remarkably
simple to define, too. That's because the data of an object in
$(\cC/B)/f$ consists of a morphism $h : X \to B$, a morphism $g : X \to
A$, and a proof $p : h = fg$. But by [[contractibility of singletons]],
the pair $(h, p)$ is redundant! The only part that actually matters is
the morphism $g : X \to A$.

One direction of the isomorphism inserts the extra (redundant!)
information, by explicitly writing out $h = fg$ and setting $p = \refl$.
Its inverse simply discards the redundant information. We construct both
of the functors here, in components.

```agda
Slice-twice : (f : Hom a b) → Functor (Slice C a) (Slice (Slice C b) (cut f))
Slice-twice f .F₀ g .domain .domain = g .domain
Slice-twice f .F₀ g .domain .map    = f ∘ g .map

Slice-twice f .F₀ g .map .map      = g .map
Slice-twice f .F₀ g .map .commutes = refl

Slice-twice f .F₁ h .map .map      = h .map
Slice-twice f .F₁ h .map .commutes = pullr (h .commutes)
Slice-twice f .F₁ h .commutes      = ext (h .commutes)

Slice-twice f .F-id    = trivial!
Slice-twice f .F-∘ g h = trivial!

Twice-slice : (f : Hom a b) → Functor (Slice (Slice C b) (cut f)) (Slice C a)
Twice-slice _ .F₀ x .domain = x .domain .domain
Twice-slice _ .F₀ x .map    = x .map .map

Twice-slice _ .F₁ h .map      = h .map .map
Twice-slice _ .F₁ h .commutes = ap map (h .commutes)

Twice-slice _ .F-id = trivial!
Twice-slice _ .F-∘ _ _ = trivial!
```

We will also need the fact that these inverses are also adjoints.

```agda
Twice⊣Slice : (f : Hom a b) → Twice-slice f ⊣ Slice-twice f
Twice⊣Slice f = adj where
  adj : Twice-slice f ⊣ Slice-twice f
  adj .unit .η x .map .map      = id
  adj .unit .η x .map .commutes = idr _ ∙ x .map .commutes
  adj .unit .η x .commutes      = ext (idr _)
  adj .unit .is-natural x y f   = ext id-comm-sym

  adj .counit .η x .map         = id
  adj .counit .η x .commutes    = idr _
  adj .counit .is-natural x y f = ext id-comm-sym

  adj .zig = ext (idr _)
  adj .zag = ext (idr _)
```
