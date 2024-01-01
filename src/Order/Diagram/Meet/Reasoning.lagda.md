<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Order.Base

import Order.Diagram.Meet
import Order.Reasoning

open Order.Diagram.Meet using (Has-meets)
```
-->

```agda
module Order.Diagram.Meet.Reasoning {o ℓ} {P : Poset o ℓ} (meets : Has-meets P) where
```

<!--
```agda
open Order.Diagram.Meet P
open Order.Reasoning P
```
-->

# Reasoning about meets

```agda
module meets {x} {y} = Meet (meets x y)
open meets renaming
  ( meet≤l to ∩≤l
  ; meet≤r to ∩≤r
  ; greatest to ∩-universal)
  public
```


```agda
infixr 25 _∩_
_∩_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
x ∩ y = meets.glb {x} {y}
```

```agda
abstract
  ∩-idem : ∀ {x} → x ∩ x ≡ x
  ∩-idem = ≤-antisym ∩≤l (∩-universal _ ≤-refl ≤-refl)

  ∩-comm : ∀ {x y} → x ∩ y ≡ y ∩ x
  ∩-comm =
    ≤-antisym
      (∩-universal _ ∩≤r ∩≤l)
      (∩-universal _ ∩≤r ∩≤l)

  ∩-assoc : ∀ {x y z} → x ∩ (y ∩ z) ≡ (x ∩ y) ∩ z
  ∩-assoc =
    ≤-antisym
      (∩-universal _
        (∩-universal _ ∩≤l (≤-trans ∩≤r ∩≤l))
        (≤-trans ∩≤r ∩≤r))
      (∩-universal _
        (≤-trans ∩≤l ∩≤l)
        (∩-universal _ (≤-trans ∩≤l ∩≤r) ∩≤r))
```

```agda
  ∩-is-semigroup : is-semigroup _∩_
  ∩-is-semigroup .has-is-magma .has-is-set = Ob-is-set
  ∩-is-semigroup .associative = ∩-assoc
```

```agda
  ∩≤∩
    : ∀ {x y x' y'}
    → x ≤ x'
    → y ≤ y'
    → (x ∩ y) ≤ (x' ∩ y')
  ∩≤∩ p q = ∩-universal _ (≤-trans ∩≤l p) (≤-trans ∩≤r q)
```

```agda
  ∩≤∩l : ∀ {x y x'} → x ≤ x' → x ∩ y ≤ x' ∩ y
  ∩≤∩l p = ∩≤∩ p ≤-refl

  ∩≤∩r : ∀ {x y y'} → y ≤ y' → x ∩ y ≤ x ∩ y'
  ∩≤∩r p = ∩≤∩ ≤-refl p
```


```agda
  ∩-path→≤ : ∀ {x y} → x ∩ y ≡ x → x ≤ y
  ∩-path→≤ {x} {y} p =
    x       =˘⟨ p ⟩
    (x ∩ y) ≤⟨ ∩≤r ⟩
    y       ≤∎

  ≤→∩-path : ∀ {x y} → x ≤ y → x ∩ y ≡ x
  ≤→∩-path {x} {y} p = ≤-antisym ∩≤l (∩-universal _ ≤-refl p)
```
