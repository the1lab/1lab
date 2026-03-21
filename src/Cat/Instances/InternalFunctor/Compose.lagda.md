<!--
```agda
open import Cat.Instances.Product
open import Cat.Functor.Base
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
  open Make-bifunctor
```
-->

```agda
  Fi∘-functor : Bifunctor (Internal-functors 𝔹 ℂ) (Internal-functors 𝔸 𝔹) (Internal-functors 𝔸 ℂ)
  Fi∘-functor = make-bifunctor λ where
    .F₀     → _Fi∘_
    .lmap f → f ◂i _
    .rmap f → _ ▸i f
    .lmap-id         → Internal-nat-path λ x → refl
    .rmap-id {a = a} → Internal-nat-path λ x → a .Fi-id
    .lmap-∘         f g → Internal-nat-path λ x → refl
    .rmap-∘ {a = a} f g → Internal-nat-path λ x → a .Fi-∘ _ _
    .lrmap          f g → Internal-nat-path λ x → f .is-naturali _ _ _
```
