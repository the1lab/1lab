<!--
```agda
open import 1Lab.Prelude

open import Data.Bool.Base
```
-->

```agda
module Data.Bool.Order where
```

# The implication ordering on Bool

```agda
private
  R : Bool → Bool → Type
  R false _     = ⊤
  R true  true  = ⊤
  R true  false = ⊥

record _≤_ (x y : Bool) : Type where
  constructor lift
  field
    .lower : R x y
```

<!--
```agda
instance
  H-Level-≤ᵇ : ∀ {x y n} → H-Level (x ≤ y) (suc n)
  H-Level-≤ᵇ = prop-instance λ x y → refl
```
-->

```agda
≤-refl : ∀ {x} → x ≤ x
≤-refl {true}  = lift tt
≤-refl {false} = lift tt

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {true}  {true}  {true}  p q = _
≤-trans {false} {true}  {true}  p q = _
≤-trans {false} {false} {true}  p q = _
≤-trans {false} {false} {false} p q = _

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym {true}  {true}  p q = refl
≤-antisym {false} {false} p q = refl
```

```agda
implies→≤ : ∀ {x y} → (So x → So y) → x ≤ y
implies→≤ {true}  {true}  f = _
implies→≤ {false} {true}  f = _
implies→≤ {false} {false} f = _
implies→≤ {true}  {false} f with () ← f so-true

≤→implies : ∀ {x y} → x ≤ y → So x → So y
≤→implies {true} {true} p q = so-true

so-antisym : ∀ {x y} → (So x → So y) → (So y → So x) → x ≡ y
so-antisym p q = ≤-antisym (implies→≤ p) (implies→≤ q)
```

```agda
and-≤l : ∀ x y → and x y ≤ x
and-≤l true true   = _
and-≤l true false  = _
and-≤l false true  = _
and-≤l false false = _

and-≤r : ∀ x y → and x y ≤ y
and-≤r true  true  = _
and-≤r true  false = _
and-≤r false true  = _
and-≤r false false = _

and-univ : ∀ x y z → x ≤ y → x ≤ z → x ≤ and y z
and-univ false _    _    _ _ = _
and-univ true  true true _ _ = _

or-≤l : ∀ x y → x ≤ or x y
or-≤l true  true  = _
or-≤l true  false = _
or-≤l false true  = _
or-≤l false false = _

or-≤r : ∀ x y → y ≤ or x y
or-≤r true  true  = _
or-≤r true  false = _
or-≤r false true  = _
or-≤r false false = _

or-univ : ∀ x y z → y ≤ x → z ≤ x → or y z ≤ x
or-univ true  true  true  _ _ = _
or-univ true  true  false _ _ = _
or-univ true  false true  _ _ = _
or-univ true  false false _ _ = _
or-univ false false false _ _ = _

≤-not : ∀ x y → x ≤ y → not y ≤ not x
≤-not true  true  _ = _
≤-not false true  _ = _
≤-not false false _ = _

not-≤ : ∀ x y → not x ≤ not y → y ≤ x
not-≤ true  true  _ = _
not-≤ true  false _ = _
not-≤ false false _ = _
```
