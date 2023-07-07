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

```agda
Unitv : Enriched-precategory V-monoidal lzero
Unitv .Obv = ⊤
Unitv .Hom-ob _ _ = Unit
Unitv .idv = ρ→
Unitv ._∘v_ f g = f V.∘ ρ← V.∘ g
Unitv .idlv f = V.cancell (unitor-r.invl ηₚ _)
Unitv .idrv f = V.elimr (unitor-r.invr ηₚ _)
Unitv .assocv f g h = ap (f V.∘_) (V.assoc _ _ _) ∙ V.assoc _ _ _
Unitv .idv-natural σ = unitor-r.to .is-natural _ _ _
Unitv .∘v-naturall σ f g =
  V.assoc _ _ _
Unitv .∘v-natural-inner f σ g =
  V.pushr (V.extendl (unitor-r.from .is-natural _ _ σ))
Unitv .∘v-naturalr f g σ =
  sym (V.assoc _ _ _) ∙ ap (f V.∘_) (sym (V.assoc _ _ _))
```
