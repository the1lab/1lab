---
description: |
  Direct categories.
---

<!--
```agda
open import Cat.Functor.Conservative
open import Cat.Prelude

open import Data.Wellfounded.Properties
open import Data.Wellfounded.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Direct.Generalized where
```

# Generalized direct categories

:::{.definition #generalized-direct-category}
A [[precategory]] $\cD$ is **direct** if the relation

$$
x \prec y := \exists(f : \cD(x, y)).\ \text{$f$ is not invertible}
$$

is a [[well-founded]] relation.
:::

<!--
```agda
module _ {od ℓd} (D : Precategory od ℓd) where
  private
    module D = Cat.Reasoning D
```
-->

```agda
  record is-generalized-direct : Type (od ⊔ ℓd) where
    _≺_ : D.Ob → D.Ob → Type ℓd
    x ≺ y = ∃[ f ∈ D.Hom x y ] ¬ D.is-invertible f

    field
      ≺-wf : Wf _≺_
```

## Closure properties

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (F : Functor C D)
  where
```
-->

If $F : \cC \to \cD$ is a [[conservative functor]] and $\cD$ is a generalized
direct category, then $\cC$ is generalized direct as well.

```agda
  conservative→reflect-direct
    : is-conservative F
    → is-generalized-direct D
    → is-generalized-direct C
  conservative→reflect-direct F-conservative D-direct = C-direct where
```

<!--
```agda
    module D where
      open Cat.Reasoning D public
      open is-generalized-direct D-direct public

    open Functor F
    open is-generalized-direct
```
-->

Note that if $F$ is conservative, then it also reflects non-invertibility
of morphisms. This lets us pull back well-foundedness of $F(x) \prec F(y)$
in $\cD$ to well-foundedness of $x \prec y$ in $\cC$.

```agda
    C-direct : is-generalized-direct C
    C-direct .≺-wf =
      reflect-wf D.≺-wf F₀ $ rec! λ f ¬f-inv →
        pure (F₁ f , ¬f-inv ⊙ F-conservative)
```
