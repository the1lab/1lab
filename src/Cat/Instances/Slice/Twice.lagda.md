<!--
```agda
open import Cat.Instances.Slice
open import Cat.Functor.Adjoint
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
simple to define, too. We start by going in the opposite direction,
sending a function $g : x \to a$ to an object over $f$. We have to
choose a domain, a map $g' : x \to b$, _and_ a map $g' \to f$ over $b$.
Using all the data we have on hand, we can choose the domain to be $x$,
the map to $b$ to be

$$
x \xto{g} a \xto{f} b{\text{,}}
$$

and the map to $f$ to be $g$ itself, since we certainly have $fg = fg$.
The rest of the construction has us faced with a few more non-choices,
but it's so simple that there's no harm in including the whole thing
here.

```agda
Slice-twice : (f : Hom a b) → Functor (Slice C a) (Slice (Slice C b) (cut f))
Slice-twice f .F₀ g .domain .domain = g .domain
Slice-twice f .F₀ g .domain .map    = f ∘ g .map

Slice-twice f .F₀ g .map .map      = g .map
Slice-twice f .F₀ g .map .commutes = refl

Slice-twice f .F₁ h .map .map      = h .map
Slice-twice f .F₁ h .map .commutes = pullr (h .commutes)
Slice-twice f .F₁ h .commutes      = /-Hom-path (h .commutes)

Slice-twice f .F-id    = /-Hom-path (/-Hom-path refl)
Slice-twice f .F-∘ g h = /-Hom-path (/-Hom-path refl)
```

Showing that this is an isomorphism is similarly straightforward, but we
detour through explicitly constructing the inverse, in components.

```agda
Twice-slice : (f : Hom a b) → Functor (Slice (Slice C b) (cut f)) (Slice C a)
Twice-slice _ .F₀ x .domain = x .domain .domain
Twice-slice _ .F₀ x .map    = x .map .map

Twice-slice _ .F₁ h .map      = h .map .map
Twice-slice _ .F₁ h .commutes = ap map (h .commutes)

Twice-slice _ .F-id = /-Hom-path refl
Twice-slice _ .F-∘ _ _ = /-Hom-path refl
```

We will also need the fact that these inverses are also adjoints.

```agda
Twice⊣Slice : (f : Hom a b) → Twice-slice f ⊣ Slice-twice f
Twice⊣Slice f = adj where
  adj : Twice-slice f ⊣ Slice-twice f
  adj .unit .η x .map .map      = id
  adj .unit .η x .map .commutes = idr _ ∙ x .map .commutes
  adj .unit .η x .commutes      = /-Hom-path (idr _)
  adj .unit .is-natural x y f   = /-Hom-path (/-Hom-path id-comm-sym)

  adj .counit .η x .map         = id
  adj .counit .η x .commutes    = idr _
  adj .counit .is-natural x y f = /-Hom-path id-comm-sym

  adj .zig = /-Hom-path (idr _)
  adj .zag = /-Hom-path (/-Hom-path (idr _))
```
