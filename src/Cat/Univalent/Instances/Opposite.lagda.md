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
opposite-is-category x .to-path i = x .to-path $
  C.make-iso (i .Cop.from) (i .Cop.to) (i .Cop.invl) (i .Cop.invr)
opposite-is-category x .to-path-over p =
  Cop.≅-pathp refl _ $ Hom-pathp-refll-iso x (C.idl _)
```
