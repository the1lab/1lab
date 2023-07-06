<!--
```agda
open import Cat.Monoidal.Base
open import Cat.Prelude

open import Cat.Enriched.Base
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
  module V = Precategory V
open Enriched-precategory
open Monoidal-category V-monoidal
```
-->

# The Unit Enriched Category

```agda
Unitv : Enriched-precategory V-monoidal lzero
Unitv .Obv = ⊤
Unitv .Homv _ _ = Unit
Unitv .idv = λ→
Unitv ._∘v_ f g = f V.∘ λ← V.∘ g
Unitv .idlv f = {!!}
Unitv .idrv = {!!}
Unitv .assocv = {!!}
Unitv .idv-natural = {!!}
Unitv .∘v-naturall = {!!}
Unitv .∘v-natural-inner = {!!}
Unitv .∘v-naturalr = {!!}
```
