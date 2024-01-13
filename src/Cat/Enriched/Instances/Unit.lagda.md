<!--
```agda
open import Cat.Monoidal.Base
open import Cat.Prelude

open import Cat.Enriched.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Enriched.Instances.Unit
  {ov ℓv} {V : Precategory ov ℓv}
  {V-monoidal : Monoidal-category V}
  where
```

<!--
```agda
private
  module V = Cat.Reasoning V
open Enriched-precategory
open Monoidal-category V-monoidal
open _=>_
```
-->

# The Unit Enriched Category

Let $\cV$ be a [[monoidal category]]. We can define a $\cV$-enriched
analog of the [[terminal category]] by using the monoidal unit of $\cV$
as a hom-object. We shall call this category the **unit category**.

```agda
Unitv : Enriched-precategory V-monoidal lzero
Unitv .Obv = ⊤
Unitv .Hom-ob _ _ = Unit
```

The identity morphism is given by the right unitor and composition
needs to use the right unitor to discharge the redundant unit.

```agda
Unitv .idv = ρ→
Unitv ._∘v_ f g = f V.∘ ρ← V.∘ g
```

The category equations follow from a quick calculation.

```agda
Unitv .idlv f = V.cancell (unitor-r.invl ηₚ _)
Unitv .idrv f = V.elimr (unitor-r.invr ηₚ _)
Unitv .assocv f g h = ap (f V.∘_) (V.assoc _ _ _) ∙ V.assoc _ _ _
```

Furthermore, naturality follows from naturality of the right unitor.

```agda
Unitv .idv-natural σ = unitor-r.to .is-natural _ _ _
Unitv .∘v-naturall σ f g =
  V.assoc _ _ _
Unitv .∘v-natural-inner f σ g =
  V.pushr (V.extendl (unitor-r.from .is-natural _ _ σ))
Unitv .∘v-naturalr f g σ =
  sym (V.assoc _ _ _) ∙ ap (f V.∘_) (sym (V.assoc _ _ _))
```
