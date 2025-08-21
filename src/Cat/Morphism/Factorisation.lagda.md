---
description: |
  Factorisations of morphisms.
---
<!--
```agda
open import Cat.Morphism.Class
open import Cat.Prelude

import Cat.Reasoning
```
-->
```agda
module Cat.Morphism.Factorisation where
```

# Factorisations

<!--
```agda
module _
  {o ℓ ℓl ℓr}
  (C : Precategory o ℓ)
  (L : Arrows C ℓl)
  (R : Arrows C ℓr)
  where
  private module C = Cat.Reasoning C
```
-->

:::{.definition #factorisation}
Let $L, R \subseteq C$ be two classes of morphisms of $\cC$.
An $(L,R)$ **factorisation** of a morphism $f : \cC(X,Y)$ consists
of an object $Im : \cC$ and a pair of morphisms $l : \cC(X,M), r : \cC(M,Y)$
such that $l \in L$, $r \in R$, and $f = r \circ l$.
:::

```agda
  record Factorisation {a b} (f : C.Hom a b) : Type (o ⊔ ℓ ⊔ ℓl ⊔ ℓr) where
    field
      mid     : C.Ob
      left    : C.Hom a mid
      right   : C.Hom mid b
      left∈L  : left ∈ L
      right∈R : right ∈ R
      factors : f ≡ right C.∘ left
```
