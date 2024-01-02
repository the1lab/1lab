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

```agda
abstract
  ∪-idem : ∀ {x} → x ∪ x ≡ x
  ∪-idem = ≤-antisym (∪-universal _ ≤-refl ≤-refl) l≤∪

  ∪-comm : ∀ {x y} → x ∪ y ≡ y ∪ x
  ∪-comm =
    ≤-antisym
      (∪-universal _ r≤∪ l≤∪)
      (∪-universal _ r≤∪ l≤∪)

  ∪-assoc : ∀ {x y z} → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  ∪-assoc =
    ≤-antisym
      (∪-universal _
        (≤-trans l≤∪ l≤∪)
        (∪-universal _ (≤-trans r≤∪ l≤∪) r≤∪))
      (∪-universal _
        (∪-universal _ l≤∪ (≤-trans l≤∪ r≤∪))
        (≤-trans r≤∪ r≤∪))
```

```agda
  ∪-is-semigroup : is-semigroup _∪_
  ∪-is-semigroup .has-is-magma .has-is-set = Ob-is-set
  ∪-is-semigroup .associative = ∪-assoc
```

```agda
  ∪≤∪
    : ∀ {x y x' y'}
    → x ≤ x'
    → y ≤ y'
    → (x ∪ y) ≤ (x' ∪ y')
  ∪≤∪ p q = ∪-universal _ (≤-trans p l≤∪) (≤-trans q r≤∪)
```

```agda
  ∪-path→≤ : ∀ {x y} → x ∪ y ≡ y → x ≤ y
  ∪-path→≤ {x} {y} p =
    x       ≤⟨ l≤∪ ⟩
    (x ∪ y) =⟨ p ⟩
    y       ≤∎

  ≤→∪-path : ∀ {x y} → x ≤ y → x ∪ y ≡ y
  ≤→∪-path p = ≤-antisym (∪-universal _ p ≤-refl) r≤∪
```
