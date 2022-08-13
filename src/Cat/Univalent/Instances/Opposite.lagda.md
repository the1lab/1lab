```agda
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning

module Cat.Univalent.Instances.Opposite
  {o ℓ} {C : Precategory o ℓ}
  where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module Cop = Cat.Reasoning (C ^op)
```
-->

# Opposites of univalent categories

A simple case of closure of univalence is the duality involution: Since
isomorphisms in $\ca{C}\op$ are the same as isomorphisms in $\ca{C}$,
the former is univalent iff the latter is.

```agda
opposite-is-category : is-category C → is-category (C ^op)
opposite-is-category x A .centre = A , Cop.id-iso
opposite-is-category x A .paths (B , isom) =
  Σ-pathp
    (iso→path C x (C.make-iso (isom .Cop.from) (isom .Cop.to) (isom .Cop.invl) (isom .Cop.invr)))
    (Cop.≅-pathp refl _ (Hom-pathp-refll-iso C x (C.idl _)))
```
