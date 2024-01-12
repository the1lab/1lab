<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Order.Diagram.Join
open import Order.Base

import Order.Reasoning
```
-->

```agda
module Order.Diagram.Join.Reasoning
  {o ℓ} {P : Poset o ℓ} {_∪_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟}
  (∪-joins : ∀ x y → is-join P x y (x ∪ y))
  where
```

<!--
```agda
open Order.Reasoning P
open Join
```
-->

# Reasoning about joins

This module provides syntax and reasoning combinators for working with
[[partial orders]] that have all [[joins]].

```agda
joins : ∀ x y → Join P x y
joins x y .lub      = x ∪ y
joins x y .has-join = ∪-joins x y

module joins {x} {y} = Join (joins x y)
open joins renaming
  ( l≤join to l≤∪
  ; r≤join to r≤∪
  ; least to ∪-universal)
  public
```

The join operation is idempotent and commutative.

```agda
abstract
  ∪-idem : ∀ {x} → x ∪ x ≡ x
  ∪-idem = ≤-antisym (∪-universal _ ≤-refl ≤-refl) l≤∪

  ∪-comm : ∀ {x y} → x ∪ y ≡ y ∪ x
  ∪-comm =
    ≤-antisym
      (∪-universal _ r≤∪ l≤∪)
      (∪-universal _ r≤∪ l≤∪)
```

Furthermore, it is associative, and thus forms a [[semigroup]].

```agda
  ∪-assoc : ∀ {x y z} → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  ∪-assoc =
    ≤-antisym
      (∪-universal _
        (≤-trans l≤∪ l≤∪)
        (∪-universal _ (≤-trans r≤∪ l≤∪) r≤∪))
      (∪-universal _
        (∪-universal _ l≤∪ (≤-trans l≤∪ r≤∪))
        (≤-trans r≤∪ r≤∪))

  ∪-is-semigroup : is-semigroup _∪_
  ∪-is-semigroup .has-is-magma .has-is-set = Ob-is-set
  ∪-is-semigroup .associative = ∪-assoc
```

Additionally, it respects the ordering on $P$, in each variable.

```agda
  ∪≤∪
    : ∀ {x y x' y'}
    → x ≤ x'
    → y ≤ y'
    → (x ∪ y) ≤ (x' ∪ y')
  ∪≤∪ p q = ∪-universal _ (≤-trans p l≤∪) (≤-trans q r≤∪)
```

<!--
```agda
  ∪≤∪l : ∀ {x y x'} → x ≤ x' → (x ∪ y) ≤ (x' ∪ y)
  ∪≤∪l p = ∪≤∪ p ≤-refl

  ∪≤∪r : ∀ {x y y'} → y ≤ y' → (x ∪ y) ≤ (x ∪ y')
  ∪≤∪r p = ∪≤∪ ≤-refl p
```
-->

Finally, we note that the join operation *determines* the order on $P$,
as witnessed by the following equivalence.

```agda
  ∪→order : ∀ {x y} → x ∪ y ≡ y → x ≤ y
  ∪→order {x} {y} p =
    x       ≤⟨ l≤∪ ⟩
    (x ∪ y) =⟨ p ⟩
    y       ≤∎

  order→∪ : ∀ {x y} → x ≤ y → x ∪ y ≡ y
  order→∪ p = ≤-antisym (∪-universal _ p ≤-refl) r≤∪

  ∪≃order : ∀ {x y} → (x ∪ y ≡ y) ≃ (x ≤ y)
  ∪≃order = prop-ext! ∪→order order→∪
```
