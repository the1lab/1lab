<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Order.Diagram.Meet
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Diagram.Meet.Reasoning
  {o ℓ} {P : Poset o ℓ} {_∩_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟}
  (∩-meets : ∀ x y → is-meet P x y (x ∩ y))
  where
```

<!--
```agda
open Order.Reasoning P
open Meet
```
-->

# Reasoning about meets

This module provides syntax and reasoning combinators for working with
[[partial orders]] that have all [[meets]].

```agda
meets : ∀ x y → Meet P x y
meets x y .glb      = x ∩ y
meets x y .has-meet = ∩-meets x y

module meets {x} {y} = Meet (meets x y)
open meets renaming
  ( meet≤l to ∩≤l
  ; meet≤r to ∩≤r
  ; greatest to ∩-universal)
  public
```

The meet operation is idempotent and commutative.

```agda
abstract
  ∩-idem : ∀ {x} → x ∩ x ≡ x
  ∩-idem = ≤-antisym ∩≤l (∩-universal _ ≤-refl ≤-refl)

  ∩-comm : ∀ {x y} → x ∩ y ≡ y ∩ x
  ∩-comm =
    ≤-antisym
      (∩-universal _ ∩≤r ∩≤l)
      (∩-universal _ ∩≤r ∩≤l)
```

Furthermore, it is associative, and thus forms a [[semigroup]].

```agda
  ∩-assoc : ∀ {x y z} → x ∩ (y ∩ z) ≡ (x ∩ y) ∩ z
  ∩-assoc =
    ≤-antisym
      (∩-universal _
        (∩-universal _ ∩≤l (≤-trans ∩≤r ∩≤l))
        (≤-trans ∩≤r ∩≤r))
      (∩-universal _
        (≤-trans ∩≤l ∩≤l)
        (∩-universal _ (≤-trans ∩≤l ∩≤r) ∩≤r))

  ∩-is-semigroup : is-semigroup _∩_
  ∩-is-semigroup .has-is-magma .has-is-set = Ob-is-set
  ∩-is-semigroup .associative = ∩-assoc
```

Additionally, it respects the ordering on $P$, in each variable.

```agda
  ∩≤∩
    : ∀ {x y x' y'}
    → x ≤ x'
    → y ≤ y'
    → (x ∩ y) ≤ (x' ∩ y')
  ∩≤∩ p q = ∩-universal _ (≤-trans ∩≤l p) (≤-trans ∩≤r q)
```

<!--
```agda
  ∩≤∩l : ∀ {x y x'} → x ≤ x' → (x ∩ y) ≤ (x' ∩ y)
  ∩≤∩l p = ∩≤∩ p ≤-refl

  ∩≤∩r : ∀ {x y y'} → y ≤ y' → (x ∩ y) ≤ (x ∩ y')
  ∩≤∩r p = ∩≤∩ ≤-refl p
```
-->

Finally, we note that the meet operation *determines* the order on $P$,
as witnessed by the following equivalence.

```agda
  ∩→order : ∀ {x y} → x ∩ y ≡ x → x ≤ y
  ∩→order {x} {y} p =
    x       =˘⟨ p ⟩
    (x ∩ y) ≤⟨ ∩≤r ⟩
    y       ≤∎

  order→∩ : ∀ {x y} → x ≤ y → x ∩ y ≡ x
  order→∩ {x} {y} p = ≤-antisym ∩≤l (∩-universal _ ≤-refl p)

  ∩≃order : ∀ {x y} → (x ∩ y ≡ x) ≃ (x ≤ y)
  ∩≃order = prop-ext! ∩→order order→∩
```
