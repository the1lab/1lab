---
description: |
  Propositions are an ordinal.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Base

open import Order.Ordinal

import Order.Ordinal.Reasoning
```
-->
```agda
module Order.Ordinal.Instances.Prop where
```

# The type of propositions is an ordinal {defines="ordinal-of-propositions"}

<!--
```agda
open Ordinal
```
-->

```agda
Ωₒ : Ordinal lzero lzero
Ωₒ .Ob = Ω
Ωₒ ._≺_ P Q = ¬ ∣ P ∣ × ∣ Q ∣
Ωₒ .≺-wf P = go where
  go : Acc (λ P Q → ¬ ∣ P ∣ × ∣ Q ∣) P
  go = acc λ Q (¬q , _) → acc λ R (_ , q) → absurd (¬q q)
Ωₒ .≺-ext {P} {Q} P≼Q Q≼P =
  Ω-ua (λ p → P≼Q ⊥Ω (id , p) .snd) (λ q → Q≼P ⊥Ω (id , q) .snd)
Ωₒ .≺-trans (¬p , q) (¬q , r) = ¬p , r
Ωₒ .≺-is-prop = hlevel 1

module Ωₒ = Order.Ordinal.Reasoning Ωₒ
```

```agda
⊥Ω-bot : ∀ P → ⊥Ω Ωₒ.≼ P
⊥Ω-bot P Q (_ , ff) = absurd ff

⊤Ω-top : ∀ P → P Ωₒ.≼ ⊤Ω
⊤Ω-top P Q (¬q , _) = ¬q , tt
```
