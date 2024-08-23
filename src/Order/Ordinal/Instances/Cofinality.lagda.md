---
description: |
  Cofinality of ordinals
---
<!--
```agda
open import 1Lab.Function.Embedding
open import 1Lab.Classical
open import 1Lab.Prelude

open import Data.Dec
open import Data.Nat
open import Data.Sum

open import Order.Ordinal.Instances.Subsingleton
open import Order.Ordinal.Instances.Plus
open import Order.Ordinal.Simulation
open import Order.Ordinal

import Order.Ordinal.Reasoning
```
-->
```agda
module Order.Ordinal.Instances.Cofinality where
```

```agda
record Cofinal
  {o ℓ o' ℓ'}
  (X : Ordinal o ℓ) (Y : Ordinal o' ℓ')
  : Type (lsuc o ⊔ lsuc ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  private
    module X = Order.Ordinal.Reasoning X
    module Y = Order.Ordinal.Reasoning Y
  field
    hom : ⌞ X ⌟ → ⌞ Y ⌟
    -- NOTE: Can also consider maps that are monotone + injective.
    cofinal : ∀ (y : ⌞ Y ⌟) → ∃[ x ∈ ⌞ X ⌟ ] (y Y.≼ hom x)
```

<!--
```agda
private variable
  o ℓ o' ℓ' o'' ℓ'' : Level
  X Y Z : Ordinal o ℓ
```
-->

If $\omega$ is the smallest ordinal equipped with a cofinal map into $\omega$,
then the law of excluded middle holds.

```agda
ω-regular-taboo : (∀ {o ℓ} → (X : Ordinal o ℓ) → Cofinal X ωₒ → Simulation ωₒ X) → LEM
ω-regular-taboo ω-regular P = dec where
  P+ω : Ordinal _ _
  P+ω = Subsingletonₒ P +ₒ ωₒ

  module P+ω = Order.Ordinal.Reasoning P+ω

  P+ω-cofinal : Cofinal P+ω ωₒ
  P+ω-cofinal .Cofinal.hom (inl x) = 0
  P+ω-cofinal .Cofinal.hom (inr x) = suc x
  P+ω-cofinal .Cofinal.cofinal n = inc (inr n , λ m m<n → ≤-sucr m<n)

  ω≤P+ω : Simulation ωₒ P+ω
  ω≤P+ω = ω-regular P+ω P+ω-cofinal

  P+ω-bot : ∀ (x : ⌞ P+ω ⌟) → ω≤P+ω # 0 P+ω.≼ x
  P+ω-bot = simulation-pres-bot ω≤P+ω λ m n m<0 → absurd (x≮0 m<0)

  dec : Dec ∣ P ∣
  dec with inspect (ω≤P+ω # 0)
  ... | inl p , eq = yes p
  ... | inr n , eq = no λ p →
    P+ω.≺-irrefl {x = inl p} (P+ω-bot (inl p) (inl p) (subst (inl p P+ω.≺_) (sym eq) (lift tt)))
```
