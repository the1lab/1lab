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

# Basic properties of monotone maps

<!--
```agda
private variable
  o ℓ : Level
  P Q : Poset o ℓ
```
-->

While we have singled out the monotone maps as the most important class
of maps between posets, the following classes of maps are also very
relevant in the study of order theory:

<!--
```
module _ {o ℓ o' ℓ'} (P : Poset o ℓ) (Q : Poset o' ℓ') (f : ⌞ P ⌟ → ⌞ Q ⌟) where
  private
    module P = Poset P
    module Q = Poset Q

  is-monotone : Type _
  is-monotone = ∀ {x y} → x P.≤ y → f x Q.≤ f y
```
-->

- :::{.definition #antitone-map}
  the **antitone maps**, which _reverse_ the order:
  :::

  ```agda
  is-antitone : Type _
  is-antitone = ∀ {x y} → x P.≤ y → f y Q.≤ f x
  ```

- :::{.definition #order-reflection}
  the **order reflections**, which, as the name imply, _reflect_ the order:
  :::

  ```agda
  is-order-reflection : Type _
  is-order-reflection = ∀ {x y} → f x Q.≤ f y → x P.≤ y
  ```

- :::{.definition #order-embedding}
  and finally, the **order embeddings**, which both preserve and reflect the
  order.
  :::

  ```agda
  is-order-embedding : Type _
  is-order-embedding = ∀ {x y} → (x P.≤ y) ≃ (f x Q.≤ f y)
  ```

  The name "order embedding" reflects the fact that any order embedding
  is also an [[embedding]] of the underlying sets:

  ```agda
  is-order-embedding→is-embedding
    : is-order-embedding → is-embedding f
  is-order-embedding→is-embedding p = injective→is-embedding! λ {x} {y} fx=fy →
    let
      x≤y = Equiv.from p (Q.≤-refl' fx=fy)
      y≤x = Equiv.from p (Q.≤-refl' (sym fx=fy))
    in P.≤-antisym x≤y y≤x
  ```

  Since the order is a proposition, even though an order embedding is
  defined to be a map which induces equivalences, this is easily seen to
  reduce to being both monotone and an order-reflection.

  ```agda
  monotone-reflection→is-order-embedding
    : is-monotone → is-order-reflection → is-order-embedding
  monotone-reflection→is-order-embedding p q .fst = p
  monotone-reflection→is-order-embedding p q .snd = biimp-is-equiv! p q
  ```

<!--
```agda
module _ {o ℓ o' ℓ'} {P : Poset o ℓ} {Q : Poset o' ℓ'} where
  private
    module P = Order.Reasoning P
    module Q = Order.Reasoning Q
```
-->

The rest of this module will be dedicated to proving various closure
properties about the classes of maps defined above. First, we turn to
the construction of order-embeddings. If $f : P \to Q$ is any function
(not necessarily monotone!) which admits a *monotone* right inverse $g :
Q \to P$, then $f$ is an order-reflection:

```agda
  section→order-reflection
    : ∀ (f : ⌞ P ⌟ → ⌞ Q ⌟) (g : Monotone Q P)
    → is-right-inverse f (g .hom)
    → is-order-reflection P Q f
  section→order-reflection f g sect {x = x} {y = y} fx≤fy =
    x           P.=˘⟨ sect x ⟩
    g # (f x)   P.≤⟨ g .pres-≤ fx≤fy ⟩
    g # (f y)   P.=⟨ sect y ⟩
    y           P.≤∎
```

As a corollary, if $f : P \to Q$ in the setup above _is_ monotone, then
it's actually an order-embedding. This means that $P$ is equivalent, as
a poset, to its image in $Q$.

```agda
  section→order-embedding
    : ∀ (f : Monotone P Q) (g : Monotone Q P)
    → is-right-inverse (f .hom) (g .hom)
    → is-order-embedding P Q (f .hom)
  section→order-embedding f g sect =
    monotone-reflection→is-order-embedding P Q _
      (f .pres-≤) (section→order-reflection (apply f) g sect)
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
  has-retract→is-order-reflection
    : (f : Hom P Q)
    → Posets.has-retract f
    → is-order-reflection P Q (apply f)
  has-retract→is-order-reflection f f-ret =
    section→order-reflection (apply f) (f-ret .retract) (λ x → f-ret .is-retract #ₚ x)

  has-retract→is-order-embedding
    : (f : Hom P Q)
    → Posets.has-retract f
    → is-order-embedding P Q (apply f)
  has-retract→is-order-embedding f f-ret =
    section→order-embedding f (f-ret .retract) (λ x → f-ret .is-retract #ₚ x)
```
-->

Since an isomorphism in $\Pos$ certainly has a monotone right inverse,
we conclude that order-isomorphisms are also order-embeddings.

```agda
  order-iso-is-order-embedding
    : (f : P ≅ Q) → is-order-embedding P Q (apply (f .Posets.to))
  order-iso-is-order-embedding f =
    has-retract→is-order-embedding (f .to) (iso→to-has-retract f)
```
