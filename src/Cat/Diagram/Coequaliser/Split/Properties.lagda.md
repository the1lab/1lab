```agda
open import Cat.Prelude

import Cat.Diagram.Coequaliser.Split as SplitCoeq
import Cat.Reasoning
import Cat.Functor.Reasoning

module Cat.Diagram.Coequaliser.Split.Properties where
```

# Properties of split coequalizers

This module proves some general properties of [split coequalisers].

[split coequalisers]: Cat.Diagram.Coequaliser.Split.html

## Absoluteness

The property of being a split coequaliser is a purely diagrammatic one, which has
the lovely property of being preserved by _all_ functors. We call such colimits
absolute.

```agda
module _ {o o′ ℓ ℓ′}
         {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
         (F : Functor C D) where
```
<!--
```agda
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    open Cat.Functor.Reasoning F
    open SplitCoeq
    variable
      A B E : C.Ob 
      f g e s t : C.Hom A B
```
-->

The proof follows the fact that functors preserve diagrams, and reduces to a bit
of symbol shuffling.

```agda
  is-split-coequaliser-absolute
    : is-split-coequaliser C f g e s t
    → is-split-coequaliser D (F₁ f) (F₁ g) (F₁ e) (F₁ s) (F₁ t)
  is-split-coequaliser-absolute
    {f = f} {g = g} {e = e} {s = s} {t = t} split-coeq = F-split-coeq
    where
      open is-split-coequaliser split-coeq

      F-split-coeq : is-split-coequaliser D _ _ _ _ _
      F-split-coeq .coequal = weave coequal
      F-split-coeq .rep-section = annihilate rep-section
      F-split-coeq .witness-section = annihilate witness-section
      F-split-coeq .commute = weave commute
```
