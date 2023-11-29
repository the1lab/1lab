<!--
```agda
open import Cat.Prelude

open import Order.Base

import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Order.Morphism where
```

# Basic Properties of Monotone Maps

<!--
```agda
private
  variable
    o ℓ : Level
    P Q : Poset o ℓ

```
-->

<!--
```agda
module _ {o ℓ o' ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q
```
-->

If $f : P \to Q$ is a section, then $f$ reflects the ordering of $Q$.

```agda
  section→reflect-≤
    : ∀ (f : Monotone P Q) (g : Monotone Q P)
    → is-right-inverse (f .hom) (g .hom)
    → ∀ {x y} → (f # x) Q.≤ (f # y) → x P.≤ y
  section→reflect-≤ f g sect {x = x} {y = y} fx≤fy =
    x                        P.=˘⟨ sect x ⟩
    g # (f # x)              P.≤⟨ g .pres-≤ fx≤fy ⟩
    g # (f # y)              P.=⟨ sect y ⟩
    y                        P.≤∎
```

As a corollary, if $f : P \to Q$ is a section, then $f$ reflects the
the orderings on $P$ is equivalent with its image in $Q$.

```agda
  section→≤-equiv
    : ∀ (f : Monotone P Q) (g : Monotone Q P)
    → is-right-inverse (f .hom) (g .hom)
    → ∀ {x y} → (x P.≤ y) ≃ (f # x Q.≤ f # y)
  section→≤-equiv f g sect =
    prop-ext! (f .pres-≤) (section→reflect-≤ f g sect)
```


<!--
```agda
module _ {o ℓ} {P Q : Poset o ℓ} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q

  open Cat.Reasoning (Posets o ℓ)
```
-->

<!--
```
  has-retract→reflects-≤
    : (f : Hom P Q)
    → Posets.has-retract f
    → ∀ {x y} → f # x Q.≤ f # y → x P.≤ y
  has-retract→reflects-≤ f f-ret =
    section→reflect-≤ f (f-ret .retract) (λ x → f-ret .is-retract #ₚ x)

  has-retract→≤-equiv
    : (f : Hom P Q)
    → Posets.has-retract f
    → ∀ {x y} → (x P.≤ y) ≃ (f # x Q.≤ f # y)
  has-retract→≤-equiv f f-ret =
    section→≤-equiv f (f-ret .retract) (λ x → f-ret .is-retract #ₚ x)

  iso→≤-equiv
    : (f : P ≅ Q)
    → ∀ {x y} → (x P.≤ y) ≃ (f .to # x Q.≤ f .to # y)
  iso→≤-equiv f = has-retract→≤-equiv (f .to) (iso→to-has-retract f)
```
-->
