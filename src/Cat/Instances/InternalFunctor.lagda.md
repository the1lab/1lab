<!--
```agda
open import Cat.Prelude

import Cat.Internal.Base
import Cat.Internal.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Instances.InternalFunctor
  {o ℓ} (C : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Reasoning C
open Cat.Internal.Base C
open Internal-hom
open Internal-functor
open _=>i_
```
-->

# Internal functor categories

Like 1-categorical natural transformations, there is an identity internal
natural transformation, and internal natural transformations are
composable.

```agda
module _ {ℂ 𝔻 : Internal-cat} where
  private
    module ℂ = Cat.Internal.Reasoning ℂ
    module 𝔻 = Cat.Internal.Reasoning 𝔻

  idnti : ∀ {F : Internal-functor ℂ 𝔻} → F =>i F
  idnti .ηi x = 𝔻.idi _
  idnti .is-naturali x y f =
    𝔻.idli _ ∙ sym (𝔻.idri _)
  idnti {F = F} .ηi-nat x σ = 𝔻.casti $
    𝔻.idi-nat σ 𝔻.∙i ap 𝔻.idi (F .Fi₀-nat x σ)

  _∘nti_ : ∀ {F G H : Internal-functor ℂ 𝔻} → G =>i H → F =>i G → F =>i H
  (α ∘nti β) .ηi x = α .ηi x 𝔻.∘i β .ηi x
  (α ∘nti β) .is-naturali x y f =
    𝔻.pullri (β .is-naturali x y f)
    ∙ 𝔻.extendli (α .is-naturali x y f)
  (α ∘nti β) .ηi-nat x σ = 𝔻.casti $
    (α .ηi x 𝔻.∘i β .ηi x) [ σ ]     𝔻.≡i⟨ 𝔻.∘i-nat (α .ηi x) (β .ηi x) σ ⟩
    α .ηi x [ σ ] 𝔻.∘i β .ηi x [ σ ] 𝔻.≡i⟨ (λ i → α .ηi-nat x σ i 𝔻.∘i β .ηi-nat x σ i) ⟩
    α .ηi (x ∘ σ) 𝔻.∘i β .ηi (x ∘ σ) ∎
```

We can then show that internal functors and internal natural
transformations form a category. This is due to the fact that paths
between internal natural transformations are solely characterised by
paths between the actions.

```agda
module _ (ℂ 𝔻 : Internal-cat) where
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻

  Internal-functors : Precategory (o ⊔ ℓ) (o ⊔ ℓ)
  Internal-functors .Precategory.Ob = Internal-functor ℂ 𝔻
  Internal-functors .Precategory.Hom F G = F =>i G
  Internal-functors .Precategory.Hom-set _ _ = Internal-nat-set
  Internal-functors .Precategory.id = idnti
  Internal-functors .Precategory._∘_ = _∘nti_
  Internal-functors .Precategory.idr α =
    Internal-nat-path λ x → 𝔻.idri _
  Internal-functors .Precategory.idl α =
    Internal-nat-path λ x → 𝔻.idli _
  Internal-functors .Precategory.assoc α β γ =
    Internal-nat-path λ x → 𝔻.associ _ _ _
```
