---
description: |
  Propositions are an ordinal.
---
<!--
```agda
open import 1Lab.Classical
open import 1Lab.Prelude

open import Data.Wellfounded.Base
open import Data.Dec
open import Data.Fin
open import Data.Nat

open import Order.Ordinal.Simulation
open import Order.Ordinal

import Order.Ordinal.Reasoning
```
-->
```agda
module Order.Ordinal.Instances.Prop where
```

# The type of propositions is an ordinal {defines="ordinal-of-propositions"}

The type $\Omega$ of propositions naturally carries the structure
of an ordinal, where $P \prec Q$ when $\lnot P \land Q$.

<!--
```agda
open Simulation
open Ordinal
```
-->

```agda
Ωₒ : Ordinal lzero lzero
Ωₒ .Ob = Ω
Ωₒ ._≺_ P Q = ¬ ∣ P ∣ × ∣ Q ∣
```

To show that $\prec$ is well-founded, observe that if $Q \prec P$, then
$\lnot R \prec P$, as we would have both $Q$ and $\lnot Q$. This means
that we only need two layers of accessiblity to reach the end of any
chain in $\Omega$.

```agda
Ωₒ .≺-wf P = go where
  go : Acc (λ P Q → ¬ ∣ P ∣ × ∣ Q ∣) P
  go = acc λ Q (¬q , _) → acc λ R (_ , q) → absurd (¬q q)
```

Extensionality follows from another straighforward argument. First, observe
that if $P \preceq Q$ then $P \to Q$: by definition, $R \prec P \to R \prec Q$
for every $R$, so we can use $\bot$ and get that $\lnot \bot \times P \to \lnot \bot \times Q$.
The rest follows by propositional extensionality!

```agda
Ωₒ .≺-ext {P} {Q} P≼Q Q≼P =
  Ω-ua (λ p → P≼Q ⊥Ω (id , p) .snd) (λ q → Q≼P ⊥Ω (id , q) .snd)
```

Finally, transitivity and thinness follow almost immediately.

```agda
Ωₒ .≺-trans (¬p , q) (¬q , r) = ¬p , r
Ωₒ .≺-is-prop = hlevel 1
```

## Properties of the ordinal of propositions

<!--
```agda
module Ωₒ = Order.Ordinal.Reasoning Ωₒ
```
-->

We can give a nice characterisation of the preorder associated to
$(\Omega, \prec)$: $P \preceq Q$ if and only if $P \to Q$.

```agda
Ω≼-equiv : ∀ {P Q : Ω} → (P Ωₒ.≼ Q) ≃ (∣ P ∣ → ∣ Q ∣)
Ω≼-equiv = Iso→Equiv $
  (λ P≼Q p → P≼Q ⊥Ω (id , p) .snd) ,
  iso (λ f R (¬r , p) → ¬r , f p)
    (λ _ → prop!)
    (λ _ → prop!)
```

This gives us an indirect way of showing that $\bot$ is a [[bottom element]]
and $\top$ is a [[top element]], but the direct proofs are honestly easier.

```agda
⊥Ω-bot : ∀ P → ⊥Ω Ωₒ.≼ P
⊥Ω-bot P Q (_ , ff) = absurd ff

⊤Ω-top : ∀ P → P Ωₒ.≼ ⊤Ω
⊤Ω-top P Q (¬q , _) = ¬q , tt
```

More interestingly, we can simulate $2$ inside of $\Omega$ by taking
$0$ to $\bot$ and $1$ to $\top$

```agda
Ωₒ-sim-2ₒ : Simulation 2 Ωₒ
Ωₒ-sim-2ₒ .hom fzero = ⊥Ω
Ωₒ-sim-2ₒ .hom (fsuc fzero) = ⊤Ω
```

<details>
<summary>Proving that this is a simulation is quite dry, so we omit the
details.
</summary>
```agda
Ωₒ-sim-2ₒ .pres-≺ {fzero} {fsuc fzero} x<y = id , tt
Ωₒ-sim-2ₒ .pres-≺ {fsuc fzero} {fsuc fzero} (s≤s ())
Ωₒ-sim-2ₒ .sim _ = fzero
Ωₒ-sim-2ₒ .sim-≺ {fsuc fzero} {P} {¬p , l} = ≤-refl
Ωₒ-sim-2ₒ .simulates {fsuc fzero} {P} {¬p , ff} = Ω-ua (λ ff → absurd ff) ¬p
```
</details>

However, the converse is a constructive taboo! More precisely, if $2$
simulates $\Omega$, then the [[law of excluded middle]] holds.

```agda
2ₒ-sim-Ωₒ→lem : Simulation Ωₒ 2 → LEM
```

Let $P$ be a proposition. Our simulation gives us a function $f : \Omega \to 2$,
so we can check if $f$ sends $P$ to $0$ or $1$.

```agda
2ₒ-sim-Ωₒ→lem f P with inspect (f # P)
```

If $f(P) = 0$, then we can show $\lnot P$. Suppose that we had some
$p : P$, and note that $\bot \prec P$, as $P$ is inhabited.
Moreover, $f$ is strictly monotone, so $f(\bot) < f(P)$. However,
$f(P) = 0$, so $f(\bot) < 0$; a contradiction!

```agda
... | fzero , fp=0 =
  no (λ p → x≮0 (≤-trans (f .pres-≺ {⊥Ω} {P} (id , p)) (≤-refl' (ap to-nat fp=0))))
```

Conversely, if $f(P) = 1$, then we can prove $P$. As $f$ is a simulation
and $f(P) \leq 1$, there must exist some $Q$ in the preimage of $0$ with
$Q \prec P$, which immediately lets us prove $P$.

```agda
... | fsuc fzero , fp=1 =
  yes (snd (f .sim-≺ {P} {0} {≤-refl' (sym (ap to-nat fp=1))}))
```
