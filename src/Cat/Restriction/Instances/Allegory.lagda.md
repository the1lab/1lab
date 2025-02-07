<!--
```agda
open import Cat.Functor.WideSubcategory
open import Cat.Restriction.Base
open import Cat.Allegory.Base
open import Cat.Prelude

import Cat.Allegory.Morphism
```
-->

```agda
module Cat.Restriction.Instances.Allegory where
```

# Restriction categories from allegories

Let $\cA$ be an [allegory], considered as a sort of generalized category
of "sets and relations". Much like we can recover a category of "sets and
functions" via the associated [category of maps], we can recover a category
of "sets and partial functions" by only restricting to [functional]
relations instead of functional _and_ [entire] relations.

[allegory]: Cat.Allegory.Base.html
[category of maps]: Cat.Allegory.Maps.html
[functional]: Cat.Allegory.Morphism.html#functional-morphisms
[entire]: Cat.Allegory.Morphism.html#entire-morphisms

<!--
```agda
module _ {o ℓ ℓ'} (A : Allegory o ℓ ℓ') where
  open Cat.Allegory.Morphism A
  open Restriction-category
  open Wide-hom
```
-->

```agda
  Partial-maps-subcat : Wide-subcat cat ℓ'
  Partial-maps-subcat .Wide-subcat.P        = is-functional
  Partial-maps-subcat .Wide-subcat.P-prop f = ≤-thin
  Partial-maps-subcat .Wide-subcat.P-id     = functional-id
  Partial-maps-subcat .Wide-subcat.P-∘      = functional-∘

  Partial-maps : Precategory o (ℓ ⊔ ℓ')
  Partial-maps = Wide Partial-maps-subcat
```

This category can be equipped with a restriction structure, defining
$\restrict{f}$ to be the [domain] of the partial maps.
Note that the first 3 axioms don't actually require the relation to be
functional; it's only relevant in the converse direction of the 4th axiom!

[domain]: Cat.Allegory.Morphism.html#domains

```agda
  Partial-maps-restriction : Restriction-category Partial-maps
  Partial-maps-restriction ._↓ f .hom = domain (f .hom)
  Partial-maps-restriction ._↓ f .witness = domain-functional (f .hom)
  Partial-maps-restriction .↓-dom f = ext $
    domain-absorb (f .hom)
  Partial-maps-restriction .↓-comm f g = ext domain-comm
  Partial-maps-restriction .↓-smashr f g = ext $
    domain-smashr (g .hom) (f .hom)
  Partial-maps-restriction .↓-swap f g = ext $
    domain-swap (f .hom) (g .hom) (g .witness)
```
