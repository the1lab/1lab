<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Instances.InternalFunctor
import Cat.Internal.Reasoning
import Cat.Internal.Base as Internal
```
-->

```agda
module Cat.Instances.InternalFunctor.Compose where
```

# Functoriality of internal functor composition

Internal functor composition is functorial, when viewed as an operation
on [internal functor categories]. This mirrors [the similar results] for
composition of ordinary functors.

[internal functor categories]: Cat.Instances.InternalFunctor.html
[the similar results]: Cat.Functor.Compose.html

To show this, we will need to define whiskering and horizontal
composition of internal natural transformations.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {𝔸 𝔹 ℂ : Internal.Internal-cat C} where
  open Precategory C
  open Internal C
  open Internal-functor
  open _=>i_
  private
    module 𝔸 = Cat.Internal.Reasoning 𝔸
    module 𝔹 = Cat.Internal.Reasoning 𝔹
    module ℂ = Cat.Internal.Reasoning ℂ
```
-->

```agda
  _◂i_
    : {F G : Internal-functor 𝔹 ℂ}
    → F =>i G → (H : Internal-functor 𝔸 𝔹) → F Fi∘ H =>i G Fi∘ H

  _▸i_
    : {F G : Internal-functor 𝔸 𝔹}
    → (H : Internal-functor 𝔹 ℂ) → F =>i G → H Fi∘ F =>i H Fi∘ G

  _◆i_
    : {F G : Internal-functor 𝔹 ℂ} {H K : Internal-functor 𝔸 𝔹}
    → F =>i G → H =>i K → F Fi∘ H =>i G Fi∘ K
```

<details>
<summary>These are almost identical to their [1-categorical
counterparts], so we omit their definitions.
</summary>

[1-categorical counterparts]: Cat.Functor.Compose.html

```agda
  (α ◂i H) .ηi x = α .ηi (H .Fi₀ x)
  (α ◂i H) .is-naturali x y f = α .is-naturali _ _ _
  (α ◂i H) .ηi-nat x σ = ℂ.begini
    α .ηi (H .Fi₀ x) [ σ ] ℂ.≡i⟨ α .ηi-nat _ σ ⟩
    α .ηi (H .Fi₀ x ∘ σ)   ℂ.≡i⟨ ap (α .ηi) (H .Fi₀-nat x σ) ⟩
    α .ηi (H .Fi₀ (x ∘ σ)) ∎

  (H ▸i α) .ηi x = H .Fi₁ (α .ηi x)
  (H ▸i α) .is-naturali x y f =
    sym (H .Fi-∘ _ _) ∙ ap (H .Fi₁) (α .is-naturali _ _ _) ∙ H .Fi-∘ _ _
  (H ▸i α) .ηi-nat x σ = ℂ.casti $
    H .Fi₁-nat _ σ ℂ.∙i λ i → H .Fi₁ (α .ηi-nat x σ i)

  _◆i_ {F} {G} {H} {K} α β .ηi x = G .Fi₁ (β .ηi x) ℂ.∘i α .ηi (H .Fi₀ x)
  _◆i_ {F} {G} {H} {K} α β .is-naturali x y f =
    (G .Fi₁ (β .ηi _) ℂ.∘i α .ηi _) ℂ.∘i F .Fi₁ (H .Fi₁ f)   ≡⟨ ℂ.pullri (α .is-naturali _ _ _) ⟩
    G .Fi₁ (β .ηi _) ℂ.∘i (G .Fi₁ (H .Fi₁ f) ℂ.∘i α .ηi _)   ≡⟨ ℂ.pullli (sym (G .Fi-∘ _ _) ∙ ap (G .Fi₁) (β .is-naturali _ _ _)) ⟩
    G .Fi₁ (K .Fi₁ f 𝔹.∘i β .ηi _) ℂ.∘i α .ηi _              ≡⟨ ℂ.pushli (G .Fi-∘ _ _) ⟩
    G .Fi₁ (K .Fi₁ f) ℂ.∘i (G .Fi₁ (β .ηi _) ℂ.∘i α .ηi _)   ∎
  _◆i_ {F} {G} {H} {K} α β .ηi-nat x σ = ℂ.begini
    (G .Fi₁ (β .ηi x) ℂ.∘i α .ηi (H .Fi₀ x)) [ σ ]       ℂ.≡i⟨ ℂ.∘i-nat _ _ _ ⟩
    G .Fi₁ (β .ηi x) [ σ ] ℂ.∘i α .ηi (H .Fi₀ x) [ σ ]   ℂ.≡i⟨ (λ i → G .Fi₁-nat (β .ηi x) σ i ℂ.∘i α .ηi-nat (H .Fi₀ x) σ i) ⟩
    G .Fi₁ (β .ηi x [ σ ]) ℂ.∘i α .ηi (H .Fi₀ x ∘ σ)     ℂ.≡i⟨ (λ i → G .Fi₁ (β .ηi-nat x σ i) ℂ.∘i α .ηi (H .Fi₀-nat x σ i)) ⟩
    G .Fi₁ (β .ηi (x ∘ σ)) ℂ.∘i α .ηi (H .Fi₀ (x ∘ σ))   ∎
```
</details>


With that out of the way, we can prove the main result.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (𝔸 𝔹 ℂ : Internal.Internal-cat C) where
  open Precategory C
  open Internal C
  open Cat.Instances.InternalFunctor C
  open Functor
  open Internal-functor
  open _=>i_
  private
    module 𝔸 = Cat.Internal.Reasoning 𝔸
    module 𝔹 = Cat.Internal.Reasoning 𝔹
    module ℂ = Cat.Internal.Reasoning ℂ
```
-->

```agda
  Fi∘-functor
    : Functor (Internal-functors 𝔹 ℂ ×ᶜ Internal-functors 𝔸 𝔹) (Internal-functors 𝔸 ℂ)
  Fi∘-functor .F₀ (F , G) = F Fi∘ G
```

<details>
<summary>Much like whiskering and horizontal composition, this is
identical to the result involving [functor composition]. The only
difference is the addition of extra naturality conditions, which are
easy to prove.
</summary>

[functor composition]: Cat.Functor.Compose.html

```agda
  Fi∘-functor .F₁ {F , G} {H , K} (α , β) = α ◆i β
  Fi∘-functor .F-id {F , G} = Internal-nat-path λ x →
    F .Fi₁ (𝔹.idi _) ℂ.∘i ℂ.idi _ ≡⟨ ap (ℂ._∘i ℂ.idi _) (F .Fi-id) ⟩
    ℂ.idi _ ℂ.∘i ℂ.idi _          ≡⟨ ℂ.idli _ ⟩
    ℂ.idi _ ∎
  Fi∘-functor .F-∘ {F , G} {H , J} {K , L} (α , β) (γ , τ) = Internal-nat-path λ x →
    K .Fi₁ (β .ηi _ 𝔹.∘i τ .ηi _) ℂ.∘i α .ηi _ ℂ.∘i γ .ηi _            ≡⟨ ℂ.pushli (K .Fi-∘ _ _) ⟩
    K .Fi₁ (β .ηi _) ℂ.∘i K .Fi₁ (τ .ηi _) ℂ.∘i α .ηi _ ℂ.∘i γ .ηi _   ≡⟨ ℂ.extend-inneri (sym (α .is-naturali _ _ _)) ⟩
    K .Fi₁ (β .ηi _) ℂ.∘i α .ηi _ ℂ.∘i H .Fi₁ (τ .ηi _) ℂ.∘i γ .ηi _   ≡⟨ ℂ.associ _ _ _ ⟩
    (K .Fi₁ (β .ηi x) ℂ.∘i α .ηi _) ℂ.∘i H .Fi₁ (τ .ηi _) ℂ.∘i γ .ηi _ ∎
```
</details>
