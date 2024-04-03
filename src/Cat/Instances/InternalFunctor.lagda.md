<!--
```agda
open import Cat.Prelude

import Cat.Internal.Reasoning
import Cat.Internal.Base
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

If $\cC$ and $\cD$ are categories internal to $\cB$, we can define the
**internal functor category** $\cC \to \cD$, mirroring the construction
of the ordinary [functor categories]. This relativisation plays a
similar role in the theory of internal categories.

[functor categories]: Cat.Functor.Base.html

Before we define the category, we need some simple constructions on
internal natural transformations. First, we note that there is an
internal identity natural transformation.

<!--
```agda
module _ {ℂ 𝔻 : Internal-cat} where
  private
    module ℂ = Cat.Internal.Reasoning ℂ
    module 𝔻 = Cat.Internal.Reasoning 𝔻
```
-->

```agda
  idnti : ∀ {F : Internal-functor ℂ 𝔻} → F =>i F
  idnti .ηi x = 𝔻.idi _
  idnti .is-naturali x y f =
    𝔻.idli _ ∙ sym (𝔻.idri _)
  idnti {F = F} .ηi-nat x σ = 𝔻.casti $
    𝔻.idi-nat σ 𝔻.∙i ap 𝔻.idi (F .Fi₀-nat x σ)
```

Next, we show that we can compose internal natural transformations
$\alpha : G \To H$ and $\beta : F \To G$ to obtain an internal
transformation $\alpha \circ \beta : F \To H$.

```agda
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

Armed with these facts, we proceed to construct the internal functor
category. Objects are internal functors $\cC \to \cD$, morphisms are
internal natural transformations $F \To G$.

```agda
module _ (ℂ 𝔻 : Internal-cat) where
  private
    module ℂ = Internal-cat ℂ
    module 𝔻 = Internal-cat 𝔻

  Internal-functors : Precategory (o ⊔ ℓ) (o ⊔ ℓ)
  Internal-functors .Precategory.Ob      = Internal-functor ℂ 𝔻
  Internal-functors .Precategory.Hom F G = F =>i G

  Internal-functors .Precategory.id  = idnti
  Internal-functors .Precategory._∘_ = _∘nti_
```

The category equations all follow from the fact that equality of
internal natural transformations is given by componentwise equality.

```agda
  Internal-functors .Precategory.Hom-set _ _ = hlevel 2
  Internal-functors .Precategory.idr α =
    Internal-nat-path λ x → 𝔻.idri _
  Internal-functors .Precategory.idl α =
    Internal-nat-path λ x → 𝔻.idli _
  Internal-functors .Precategory.assoc α β γ =
    Internal-nat-path λ x → 𝔻.associ _ _ _
```

## Internal natural isomorphisms

To continue our relativisation project, we can define the **internal
natural isomorphisms** to be the natural isomorphisms in an internal
functor category.

<!--
```agda
module _ {ℂ 𝔻 : Internal-cat} where
  private
    module ℂ = Cat.Internal.Reasoning ℂ
    module 𝔻 = Cat.Internal.Reasoning 𝔻
    module ℂ𝔻 = Cat.Reasoning (Internal-functors ℂ 𝔻)
```
-->

```agda
  Internal-Inversesⁿ
    : {F G : Internal-functor ℂ 𝔻}
    → F =>i G → G =>i F
    → Type _
  Internal-Inversesⁿ = ℂ𝔻.Inverses

  is-internal-natural-invertible
    : {F G : Internal-functor ℂ 𝔻}
    → F =>i G
    → Type _
  is-internal-natural-invertible = ℂ𝔻.is-invertible

  Internal-natural-iso : (F G : Internal-functor ℂ 𝔻) → Type _
  Internal-natural-iso F G = F ℂ𝔻.≅ G
```

<!--
```agda
  module Internal-Inversesⁿ
    {F G : Internal-functor ℂ 𝔻}
    {α : F =>i G} {β : G =>i F}
    (inv : Internal-Inversesⁿ α β) = ℂ𝔻.Inverses inv
  module is-internal-natural-invertible
    {F G : Internal-functor ℂ 𝔻}
    {α : F =>i G}
    (inv : is-internal-natural-invertible α) = ℂ𝔻.is-invertible inv
  module Internal-natural-iso
    {F G : Internal-functor ℂ 𝔻}
    (eta : Internal-natural-iso F G) = ℂ𝔻._≅_ eta

  record make-internal-natural-iso (F G : Internal-functor ℂ 𝔻) : Type (o ⊔ ℓ) where
    field
      etai : ∀ {Γ} (x : Hom Γ ℂ.C₀) → 𝔻.Homi (F .Fi₀ x) (G .Fi₀ x)
      invi : ∀ {Γ} (x : Hom Γ ℂ.C₀) → 𝔻.Homi (G .Fi₀ x) (F .Fi₀ x)
      etai∘invi : ∀ {Γ} (x : Hom Γ ℂ.C₀) → etai x 𝔻.∘i invi x ≡ 𝔻.idi _
      invi∘etai : ∀ {Γ} (x : Hom Γ ℂ.C₀) → invi x 𝔻.∘i etai x ≡ 𝔻.idi _
      naturali : ∀ {Γ} (x y : Hom Γ ℂ.C₀) (f : ℂ.Homi x y)
               → etai y 𝔻.∘i F .Fi₁ f ≡ G .Fi₁ f 𝔻.∘i etai x
      etai-nat : ∀ {Γ Δ} (x : Hom Δ ℂ.C₀)
               → (σ : Hom Γ Δ)
               → PathP (λ i → 𝔻.Homi (F .Fi₀-nat x σ i) (G .Fi₀-nat x σ i))
                   (etai x [ σ ]) (etai (x ∘ σ))
      invi-nat : ∀ {Γ Δ} (x : Hom Δ ℂ.C₀)
               → (σ : Hom Γ Δ)
               → PathP (λ i → 𝔻.Homi (G .Fi₀-nat x σ i) (F .Fi₀-nat x σ i))
                   (invi x [ σ ]) (invi (x ∘ σ))

  to-internal-natural-iso
    : {F G : Internal-functor ℂ 𝔻}
    → make-internal-natural-iso F G
    → Internal-natural-iso F G
  to-internal-natural-iso {F = F} {G = G} mk = ni where
    open make-internal-natural-iso mk
    open Internal-natural-iso {F} {G}
    open Internal-Inversesⁿ {F} {G}

    ni : Internal-natural-iso F G
    ni .to .ηi = etai
    ni .to .is-naturali = naturali
    ni .to .ηi-nat = etai-nat
    ni .from .ηi = invi
    ni .from .is-naturali x y f =
      invi y 𝔻.∘i G .Fi₁ f                         ≡⟨ ap (invi y 𝔻.∘i_) (sym (𝔻.idri _) ∙ ap (G .Fi₁ _ 𝔻.∘i_) (sym (etai∘invi x))) ⟩
      invi y 𝔻.∘i G .Fi₁ f 𝔻.∘i etai x 𝔻.∘i invi x ≡⟨ ap (invi y 𝔻.∘i_) (𝔻.extendli (sym (naturali _ _ _))) ⟩
      invi y 𝔻.∘i etai y 𝔻.∘i F .Fi₁ f 𝔻.∘i invi x ≡⟨ 𝔻.cancelli (invi∘etai y) ⟩
      F .Fi₁ f 𝔻.∘i invi x                         ∎
    ni .from .ηi-nat = invi-nat
    ni .inverses .invl = Internal-nat-path etai∘invi
    ni .inverses .invr = Internal-nat-path invi∘etai
```
-->
