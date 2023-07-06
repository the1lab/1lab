<!--
```agda
open import Cat.Monoidal.Base
open import Cat.Instances.EnrichedFunctor
open import Cat.Instances.Product
open import Cat.Prelude

open import Cat.Enriched.Base

import Cat.Reasoning
import Cat.Enriched.Reasoning
```
-->

```agda
module Cat.Instances.EnrichedFunctor.Compose
  {ov ℓv} {V : Precategory ov ℓv}
  {V-monoidal : Monoidal-category V}
  where
```

<!--
```agda
private
  module V = Cat.Reasoning V
open Monoidal-category V-monoidal
```
-->

# Functoriality of Enriched functor composition

```agda
module _
  {oc od oe}
  {C : Enriched-precategory V-monoidal oc}
  {D : Enriched-precategory V-monoidal od}
  {E : Enriched-precategory V-monoidal oe}
  where
  private
    module C = Cat.Enriched.Reasoning C
    module D = Cat.Enriched.Reasoning D
    module E = Cat.Enriched.Reasoning E
    open Enriched-functor
    open _=>v_
```

```agda
  _◂v_
    : {F G : Enriched-functor D E}
    → F =>v G → (H : Enriched-functor C D)
    → F Fv∘ H =>v G Fv∘ H

  _▸v_
    : {F G : Enriched-functor C D}
    → (H : Enriched-functor D E) → F =>v G
    → H Fv∘ F =>v H Fv∘ G

  _◆v_
    : {F G : Enriched-functor D E} {H K : Enriched-functor C D}
    → F =>v G → H =>v K
    → F Fv∘ H =>v G Fv∘ K
```

```agda
  (α ◂v H) .ηv Γ x = α .ηv Γ (H .Fv₀ x)
  (α ◂v H) .is-naturalv f = α .is-naturalv (H .Fv₁ f)
  (α ◂v H) .ηv-natural σ = α .ηv-natural σ

  (H ▸v α) .ηv Γ x = H .Fv₁ (α .ηv Γ x)
  (H ▸v α) .is-naturalv f =
    sym (H .Fv-∘ _ _)
    ·· ap (H .Fv₁) (α .is-naturalv f)
    ·· H .Fv-∘ _ _
  (H ▸v α) .ηv-natural σ =
    H .Fv-naturalr (α .ηv _ _) σ
    ∙ ap (H .Fv₁) (α .ηv-natural σ)
    ∙ sym (H .Fv-naturall σ (α .ηv _ _))

  _◆v_ {F} {G} {H} {K} α β .ηv Γ x =
    G .Fv₁ (β .ηv Γ x) E.∘v α .ηv Γ (H .Fv₀ x)
  _◆v_ {F} {G} {H} {K} α β .is-naturalv f =
    E.pullrv (α .is-naturalv (H .Fv₁ f))
    ·· E.pulllv (sym (G .Fv-∘ _ _) ∙ ap (G .Fv₁) (β .is-naturalv f))
    ·· E.pushlv (G .Fv-∘ _ _)
  _◆v_ {F} {G} {H} {K} α β .ηv-natural σ =
    (G .Fv₁ (β .ηv _ _) E.∘v α .ηv _ _) V.∘ σ         ≡⟨ E.∘v-naturalr _ _ σ ⟩
    G .Fv₁ (β .ηv _ _) E.∘v ⌜ α .ηv _ _ V.∘ σ ⌝       ≡⟨ ap! (α .ηv-natural σ) ⟩
    G .Fv₁ (β .ηv _ _) E.∘v ((_ ▶ σ) V.∘ α .ηv _ _)   ≡⟨ E.∘v-natural-inner _ σ _ ⟩
    ⌜ G .Fv₁ (β .ηv _ _) V.∘ σ ⌝ E.∘v α .ηv _ _       ≡⟨ ap! (G .Fv-naturalr (β .ηv _ _) σ) ⟩
    G .Fv₁ ⌜ β .ηv _ _ V.∘ σ ⌝ E.∘v α .ηv _ _         ≡⟨ ap! (β .ηv-natural σ) ⟩
    ⌜ G .Fv₁ ((_ ▶ σ) V.∘ β .ηv _ _) ⌝ E.∘v α .ηv _ _ ≡˘⟨ ap¡ (G .Fv-naturall σ (β .ηv _ _)) ⟩
    ((_ ▶ σ) V.∘ G .Fv₁ (β .ηv _ _)) E.∘v α .ηv _ _   ≡˘⟨ E.∘v-naturall σ _ _ ⟩
    (_ ▶ σ) V.∘ (G .Fv₁ (β .ηv _ _) E.∘v α .ηv _ _)   ∎
```

```agda
module _
  {oc od oe}
  (C : Enriched-precategory V-monoidal oc)
  (D : Enriched-precategory V-monoidal od)
  (E : Enriched-precategory V-monoidal oe)
  where
  private
    module C = Cat.Enriched.Reasoning C
    module D = Cat.Enriched.Reasoning D
    module E = Cat.Enriched.Reasoning E
    open Functor
    open Enriched-functor
    open _=>v_

  Fv∘-functor : Functor (VCat[ D , E ] ×ᶜ VCat[ C , D ]) VCat[ C , E ]
  Fv∘-functor .F₀ (F , G) = F Fv∘ G
  Fv∘-functor .F₁ (α , β) = α ◆v β
  Fv∘-functor .F-id {F , G} = Enriched-nat-path λ Γ x →
    E.idrv _ ∙ F .Fv-id
  Fv∘-functor .F-∘ {F , G} {H , K} {J , L} (α , β) (γ , τ) = Enriched-nat-path λ Γ x →
    E.pushlv (J .Fv-∘ _ _)
    ·· E.extend-innerv (sym (α .is-naturalv (τ .ηv Γ x)))
    ·· E.assocv _ _ _
```
