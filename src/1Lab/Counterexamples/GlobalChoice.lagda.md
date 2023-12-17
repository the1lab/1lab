<!--
```agda
open import 1Lab.Prelude

open import Data.Bool
open import Data.Dec
```
-->

```agda
module 1Lab.Counterexamples.GlobalChoice where
```

# Global choice is inconsistent with univalence {defines="global-choice"}

The principle of **global choice** says that we have a function $\| A \| \to A$ for
any type $A$. We show that this is inconsistent with univalence.

```agda
Global-choice : Typeω
Global-choice = ∀ {ℓ} (A : Type ℓ) → ∥ A ∥ → A

module _ (global-choice : Global-choice) where
```

The idea will be to apply the global choice operator to a *loop* of types, making
it contradict itself: since the argument to `global-choice`{.Agda} is a proposition,
we should get the same answer at both endpoints, so picking a non-trivial loop
will yield a contradiction.

We pick the loop on `Bool`{.Agda} that swaps the two elements.

```agda
  swap : Bool ≡ Bool
  swap = ua (not , not-is-equiv)
```

The type of booleans is inhabited, so we can apply global choice to it.

```agda
  Bool-inhabited : ∥ Bool ∥
  Bool-inhabited = inc false

  b : Bool
  b = global-choice Bool Bool-inhabited
```

Since `∥ swap i ∥`{.Agda} is a proposition, we get a loop on `Bool-inhabited`{.Agda}
over `swap`{.Agda}.

```agda
  irrelevant : PathP (λ i → ∥ swap i ∥) Bool-inhabited Bool-inhabited
  irrelevant = is-prop→pathp (λ _ → is-prop-∥-∥) Bool-inhabited Bool-inhabited
```

Hence `b`{.Agda} negates to itself, which is a contradiction.

```agda
  b≡[swap]b : PathP (λ i → swap i) b b
  b≡[swap]b i = global-choice (swap i) (irrelevant i)

  b≡notb : b ≡ not b
  b≡notb = from-pathp⁻ b≡[swap]b

  ¬global-choice : ⊥
  ¬global-choice = not-no-fixed b≡notb
```

## ∞-excluded middle is inconsistent with univalence {defines="LEM-infty"}

As a corollary, we also get that the "naïve" statement of the [[law of excluded
middle]], saying that *every* type is [[decidable]], is inconsistent with univalence.

First, since $\| A \| \to \neg \neg A$, we get that the naïve formulation of
double negation elimination is false:

```agda
¬DNE∞ : (∀ {ℓ} (A : Type ℓ) → ¬ ¬ A → A) → ⊥
¬DNE∞ dne∞ = ¬global-choice λ A a → dne∞ A (λ ¬A → ∥-∥-rec! ¬A a)
```

Thus $\rm{LEM}_\infty$, which is equivalent to $\rm{DNE}_\infty$, also fails:

```agda
¬LEM∞ : (∀ {ℓ} (A : Type ℓ) → Dec A) → ⊥
¬LEM∞ lem∞ = ¬DNE∞ λ A ¬¬a → Dec-rec id (λ ¬a → absurd (¬¬a ¬a)) (lem∞ A)
```
