<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Order.Base

import Order.Diagram.Lub
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Lub.Reasoning {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Reasoning P
open Order.Diagram.Lub P public
```
-->

# Reasoning about least upper bounds

## Joins

```agda
module Joins (joins : ∀ x y → Join x y) where
```

```agda
  module joins {x} {y} = Join (joins x y)
  open joins renaming
    ( l≤join to l≤∪
    ; r≤join to r≤∪
    ; least to ∪-universal)
    public
```

```agda
  infixr 24 _∪_
  _∪_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
  x ∪ y = joins.lub {x} {y}
```

```agda
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

## Least upper bounds

```agda
module Lubs (lubs : ∀ {I : Type o} → (f : I → Ob) → Lub f) where
  module lubs {I} {f : I → Ob} = Lub (lubs f)
  open lubs using () renaming (fam≤lub to ⋃-inj; least to ⋃-universal)

  ⋃ : ∀ {I : Type o} → (I → Ob) → Ob
  ⋃ f = lubs.lub {f = f}
```

```agda
  ⋃-twice
    : ∀ {I : Type o} {J : I → Type o} (F : (i : I) → J i → Ob)
    → ⋃ (λ i → ⋃ λ j → F i j)
    ≡ ⋃ {I = Σ I J} (λ p → F (p .fst) (p .snd))
  ⋃-twice F = ≤-antisym
    (⋃-universal _ (λ i → ⋃-universal _ (λ j → ⋃-inj _)))
    (⋃-universal _ λ (i , j) → ≤-trans (⋃-inj j) (⋃-inj i))
```

```agda
  ⋃≤⋃
    : ∀ {I : Type o} {f g : I → Ob}
    → (∀ i → f i ≤ g i)
    → ⋃ f ≤ ⋃ g
  ⋃≤⋃ p = ⋃-universal _ (λ i → ≤-trans (p i) (⋃-inj _))

  ⋃-singleton
    : ∀ {I : Type o} {f : I → Ob}
    → (p : is-contr I)
    → ⋃ f ≡ f (p .centre)
  ⋃-singleton {f = f} p = ≤-antisym
    (⋃-universal _ λ i → path→≥ $ ap f (p .paths i))
    (⋃-inj _)
```

```agda
  opaque
    has-joins : ∀ x y → Join x y
    has-joins x y = Lub→Join (lower-lub (lubs _))

  opaque
    has-bottom : Bottom
    has-bottom = Lub→Bottom (lower-lub (lubs (λ ())))

  open Joins has-joins public
  open Bottom has-bottom using (bot; ¡) public
```

```agda
  ∪-distrib-⋃-≤l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ⋃ (λ i → x ∪ f i) ≤ x ∪ ⋃ f 
  ∪-distrib-⋃-≤l =
    ⋃-universal _ λ i → ∪-universal _ l≤∪ (≤-trans (⋃-inj i) r≤∪)
```

```agda
  ∪-distrib-nonempty-⋃-l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ∥ I ∥
    → ⋃ (λ i → x ∪ f i) ≡ x ∪ ⋃ f 
  ∪-distrib-nonempty-⋃-l i =
    ≤-antisym
      ∪-distrib-⋃-≤l
      (∥-∥-rec! (λ i → ∪-universal _ (≤-trans l≤∪ (⋃-inj i)) (⋃≤⋃ λ _ → r≤∪)) i)
```

```agda
  ⋃-ap
    : ∀ {I I' : Type o} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋃ f ≡ ⋃ g
  ⋃-ap e p = ap₂ (λ I f → ⋃ {I = I} f) (ua e) (ua→ p)
  
  -- raised i for "index", raised f for "family"
  ⋃-apⁱ : ∀ {I I' : Type o} {f : I' → Ob} (e : I ≃ I') → ⋃ (λ i → f (e .fst i)) ≡ ⋃ f
  ⋃-apᶠ : ∀ {I : Type o} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋃ f ≡ ⋃ g
  
  ⋃-apⁱ e = ⋃-ap e (λ i → refl)
  ⋃-apᶠ p = ⋃-ap (_ , id-equiv) p
```
