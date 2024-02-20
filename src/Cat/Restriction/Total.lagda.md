<!--
```agda
open import Cat.Functor.WideSubcategory
open import Cat.Functor.Properties
open import Cat.Restriction.Base
open import Cat.Prelude

import Cat.Restriction.Reasoning
```
-->

```agda
module Cat.Restriction.Total where
```

# The subcategory of total maps

Let $\cC$ be a restriction category. We can construct a
[wide subcategory] of $\cC$ containing only the [total maps] of $\cC$,
denoted $\thecat{Total}(\cC)$.

[wide subcategory]: Cat.Functor.WideSubcategory.html
[total maps]: Cat.Restriction.Reasoning.html#total-morphisms

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (C↓ : Restriction-category C) where
  open Cat.Restriction.Reasoning C↓
```
-->

```agda
  Total-wide-subcat : Wide-subcat C ℓ
  Total-wide-subcat .Wide-subcat.P      = is-total
  Total-wide-subcat .Wide-subcat.P-prop = is-total-is-prop
  Total-wide-subcat .Wide-subcat.P-id   = id-total
  Total-wide-subcat .Wide-subcat.P-∘    = total-∘

  Total-maps : Precategory o ℓ
  Total-maps = Wide Total-wide-subcat
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {C↓ : Restriction-category C} where
  open Cat.Restriction.Reasoning C↓
```
-->

Furthermore, the injection from $\thecat{Total}(\cC)$ into $\cC$ is
[pseudomonic], as all isomorphisms in $\cC$ are total.

[pseudomonic]: Cat.Functor.Properties.html#pseudomonic-functors

```agda

  Forget-total : Functor (Total-maps C↓) C
  Forget-total = Forget-wide-subcat

  Forget-total-pseudomonic : is-pseudomonic Forget-total
  Forget-total-pseudomonic =
    is-pseudomonic-Forget-wide-subcat invertible→total
```
