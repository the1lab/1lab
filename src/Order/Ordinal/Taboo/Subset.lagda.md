---
description: |
  Closure of ordinals under subsets implies LEM.
---
<!--
```agda
open import 1Lab.Prelude
open import 1Lab.Classical

open import Order.Ordinal.Instances.Prop
open import Order.Ordinal
```
-->
```agda
module Order.Ordinal.Taboo.Subset where
```

# Closure of ordinals under subsets implies excluded middle

In this module, we prove that closure of ordinals under subsets implies
the [[law of excluded middle]]. Our proof follows the one in [@TypeTopology].

To start, recall that [[propositions form an ordinal|ordinal-of-propositions]],
where $P \prec Q$ if $\lnot P \land Q$. Next, consider the subset of propositions
that are not false.

```agda
¬¬Ω : Type
¬¬Ω = Σ[ P ∈ Ω ] ¬ ¬ ∣ P ∣

¬¬Ω↪Ω : ¬¬Ω ↪ Ω
¬¬Ω↪Ω = fst , Subset-proj-embedding (λ P → hlevel 1)
```

The taboo follows almost immediately. In particular, if the restriction
of $P \prec Q$ to not false propositions is extensional, then we
get [[double negation elimination]].

```agda
¬¬Ω-≺-ext→dne
  : (∀ (P Q : ¬¬Ω)
     → (∀ (R : ¬¬Ω) → R .fst Ωₒ.≺ P .fst → R .fst Ωₒ.≺ Q .fst)
     → (∀ (R : ¬¬Ω) → R .fst Ωₒ.≺ Q .fst → R .fst Ωₒ.≺ P .fst)
     → P ≡ Q)
  → DNE
```

First, observe that the ordering on non-false propositions is trivial,
as no non-false proposition can be strictly smaller than another!

```agda
¬¬Ω-≺-ext→dne ≺-ext = dne where
  ≺-trivial : ∀ (P Q : ¬¬Ω) → P .fst Ωₒ.≺ Q .fst → ⊥
  ≺-trivial (P , ¬¬p) (Q , ¬¬q) (¬p , _) = absurd (¬¬p ¬p)
```

This in turn implies that the induced preorder is trivial, IE:
for any non-false $P, Q$, we have $P \preceq Q$.

```agda
  ≼-trivial : ∀ (P Q R : ¬¬Ω) → R .fst Ωₒ.≺ P .fst → R .fst Ωₒ.≺ Q .fst
  ≼-trivial P Q R R≺P = absurd (≺-trivial R P R≺P)
```

Furthermore, this means that the type of non-false propositions is a
proposition[^1].

[^1]: In fact, it is contractible!

```agda
  ¬¬Ω-is-prop : is-prop ¬¬Ω
  ¬¬Ω-is-prop P Q = ≺-ext P Q (≼-trivial P Q) (≼-trivial Q P)
```

This means that non-false propositions are stable under double
negation, which directly implies double negation elimination.

```agda
  ¬¬P=P : (P : ¬¬Ω) → ¬Ω ¬Ω (P .fst) ≡ (P .fst)
  ¬¬P=P (P , ¬¬p) =
    ap fst (¬¬Ω-is-prop (¬Ω ¬Ω P , λ ¬¬¬p → absurd (¬¬¬p ¬¬p)) (P , ¬¬p))

  dne : DNE
  dne P ¬¬p = transport (ap ∣_∣ (¬¬P=P (P , ¬¬p))) ¬¬p
```
