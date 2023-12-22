<!--
```agda
open import Algebra.Semigroup
open import Algebra.Magma

open import Cat.Prelude

open import Order.Base

import Order.Diagram.Glb
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Glb.Reasoning {o ℓ} (P : Poset o ℓ) where
```

<!--
```agda
open Order.Reasoning P
open Order.Diagram.Glb P
```
-->

# Reasoning about greatest lower bounds

## Meets

```agda
module Meets (meets : ∀ x y → Meet x y) where
```

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

## Greatest lower bounds

```agda
module Glbs (glbs : ∀ {I : Type o} → (f : I → Ob) → Glb f) where
  module glbs {I} {f : I → Ob} = Glb (glbs f)
  open glbs using () renaming (glb≤fam to ⋂-proj; greatest to ⋂-universal) public

  ⋂ : ∀ {I : Type o} → (I → Ob) → Ob
  ⋂ f = glbs.glb {f = f}
```

```agda
  ⋂-twice
    : ∀ {I : Type o} {J : I → Type o} (f : (i : I) → J i → Ob)
    → ⋂ (λ i → ⋂ λ j → f i j)
    ≡ ⋂ {I = Σ I J} (λ p → f (p .fst) (p .snd))
  ⋂-twice f =
    ≤-antisym
      (⋂-universal _ (λ (i , j) → ≤-trans (⋂-proj i) (⋂-proj {f = f i} j)))
      (⋂-universal _ λ i → ⋂-universal _ λ j → ⋂-proj (i , j))
```

```agda
  ⋂≤⋂
    : {I : Type o} {f g : I → Ob}
    → (∀ i → f i ≤ g i)
    → ⋂ f ≤ ⋂ g
  ⋂≤⋂ p = ⋂-universal _ λ i → ≤-trans (⋂-proj i) (p i)

  ⋂-singleton
    : ∀ {I : Type o} {f : I → Ob}
    → (p : is-contr I)
    → ⋂ f ≡ f (p .centre)
  ⋂-singleton {f = f} p =
    ≤-antisym
      (⋂-proj (p .centre))
      (⋂-universal _ λ i → path→≤ (ap f (p .paths i)))
```

```agda
  opaque
    has-meets : ∀ x y → Meet x y
    has-meets x y = Glb→Meet (lower-glb (glbs _))

  opaque
    has-top : Top
    has-top = Glb→Top (lower-glb (glbs (λ ())))

  open Meets has-meets public
  open Top has-top using (top; !) public
```

```agda
  ∩-distrib-⋂-≤l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → x ∩ ⋂ f ≤ ⋂ λ i → x ∩ f i
  ∩-distrib-⋂-≤l =
    (⋂-universal _ λ i → ∩-universal _ ∩≤l (≤-trans ∩≤r (⋂-proj i)))
```

```agda
  ∩-distrib-nonempty-⋂-l
    : ∀ {I : Type o} {x : Ob} {f : I → Ob}
    → ∥ I ∥
    → x ∩ ⋂ f ≡ ⋂ λ i → x ∩ f i
  ∩-distrib-nonempty-⋂-l i =
    ≤-antisym
     ∩-distrib-⋂-≤l
     (∥-∥-rec! (λ i → ∩-universal _ (≤-trans (⋂-proj i) ∩≤l) (⋂≤⋂ λ _ → ∩≤r)) i)
```

```agda
  ⋂-ap
    : ∀ {I I' : Type o} {f : I → Ob} {g : I' → Ob}
    → (e : I ≃ I')
    → (∀ i → f i ≡ g (e .fst i))
    → ⋂ f ≡ ⋂ g
  ⋂-ap e p = ap₂ (λ I f → ⋂ {I = I} f) (ua e) (ua→ p)
  
  -- raised i for "index", raised f for "family"
  ⋂-apⁱ : ∀ {I I' : Type o} {f : I' → Ob} (e : I ≃ I') → ⋂ (λ i → f (e .fst i)) ≡ ⋂ f
  ⋂-apᶠ : ∀ {I : Type o} {f g : I → Ob} → (∀ i → f i ≡ g i) → ⋂ f ≡ ⋂ g
  
  ⋂-apⁱ e = ⋂-ap e (λ i → refl)
  ⋂-apᶠ p = ⋂-ap (_ , id-equiv) p
```
