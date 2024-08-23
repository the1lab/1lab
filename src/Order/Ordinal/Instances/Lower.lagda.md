---
description: |
  Lower sets of an ordinal.
---
<!--
```agda
open import Cat.Prelude

open import Data.Wellfounded.Base

open import Order.Ordinal.Simulation
open import Order.Ordinal

import Order.Ordinal.Reasoning
```
-->
```agda
module Order.Ordinal.Instances.Lower where
```

# Lower segments of an ordinal

<!--
```agda
open Simulation
```
-->

```agda
Lowerₒ : ∀ {o ℓ} → (X : Ordinal o ℓ) → ⌞ X ⌟ → Ordinal (o ⊔ ℓ) ℓ
Lowerₒ X x = ord module Lower where
  open Order.Ordinal.Reasoning X

  ord : Ordinal _ _
  ord .Ordinal.Ob = Σ[ a ∈ ⌞ X ⌟ ] (a ≺ x)
  ord .Ordinal._≺_ = _≺_ on fst
  ord .Ordinal.≺-wf = pullback-wf ≺-wf fst
  ord .Ordinal.≺-ext {a , a≺x} {b , b≺x} a≼b b≼a =
    Σ-prop-path! $ ≺-ext
      (λ c c≺a → a≼b (c , ≺-trans c≺a a≺x) c≺a)
      (λ c c≺b → b≼a (c , ≺-trans c≺b b≺x) c≺b)
  ord .Ordinal.≺-trans = ≺-trans
  ord .Ordinal.≺-is-prop = hlevel 1
```

<!--
```agda
{-# DISPLAY Lower.ord X x = Lowerₒ X x #-}
```
-->

```agda
module _ {o ℓ} {X : Ordinal o ℓ} {x : ⌞ X ⌟} where
  private module X = Order.Ordinal.Reasoning X

  segment : Simulation (Lowerₒ X x) X
  segment .hom = fst
  segment .pres-≺ x≺y = x≺y
  segment .sim {a , a≺x} {y} y≺a = y , X.≺-trans y≺a a≺x
  segment .sim-≺ {p = y≺a} = y≺a
  segment .simulates = refl
```
