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
of an object $m(f) : \cC$ and a pair of morphisms $l : \cC(X,m(f)), r : \cC(m(f),Y)$
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

<!--
```agda
module _
  {o ℓ ℓl ℓr}
  {C : Precategory o ℓ}
  {L : Arrows C ℓl}
  {R : Arrows C ℓr}
  where
  private module C = Cat.Reasoning C
  open Factorisation
```
-->

## Properties of factorisations

If $f$ is [[monic]] and factors as $f = r \circ l$, then $l$ must also be
monic.

```agda
  factor-monic→left-monic
    : ∀ {x y} {f : C.Hom x y}
    → (f-fac : Factorisation C L R f)
    → C.is-monic f
    → C.is-monic (f-fac .left)
  factor-monic→left-monic {f = f} f-fac f-monic = C.monic-cancell $
    C.subst-is-monic (f-fac .factors) f-monic
```

If $f$ is [[epic]] and factors as $f = r \circ l$, then $r$ must also be
epic.

```agda
  factor-epic→right-epic
    : ∀ {x y} {f : C.Hom x y}
    → (f-fac : Factorisation C L R f)
    → C.is-epic f
    → C.is-epic (f-fac .right)
  factor-epic→right-epic {f = f} f-fac f-epic = C.epic-cancelr $
    C.subst-is-epic (f-fac .factors) f-epic
```
