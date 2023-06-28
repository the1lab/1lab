<!--
```agda
open import 1Lab.Prelude
open import Data.Rel.Closure
open import Data.Wellfounded.Base
```
-->

```agda
module Rewriting.StronglyNormalising where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  _↝_ : A → A → Type ℓ
```
-->

# Strongly Normalising Rewrite Systems

An abstract rewriting system is **strongly normalising** if its
[transitive closure] is a [well-founded relation].

[transitive closure]: Data.Rel.Closure.html#transitive-closure
[well-founded relation]: Data.Wellfounded.Base.html

```agda
is-strongly-normalising : (A → A → Type ℓ) → Type _
is-strongly-normalising _↝_ = Wf (λ x y → Trans _↝_ y x)
```

This definition is classically equivalent to the non-existence of infinite
reduction sequences. However, strong normalisation is more useful
constructively, as we can use it to perform induction. However, the
latter notion is still useful; we call such rewrite systems **terminating**.

```agda
is-terminating : (A → A → Type ℓ) → Type _
is-terminating {A = A} _↝_ = 
  ¬ (∃[ aₙ ∈ (Nat → A) ] (∀ n → Trans _↝_ (aₙ n) (aₙ (suc n))))
```

If a rewrite system is strongly normalising, then it is terminating.
Aiming for a contradiction, let us assume that we have some infinite
chain $a_0 \leadsto a_1 \leadsto \cdots$ of reductions. We then perform
well-founded induction where our motive states that, for all $n$, there
is no reduction $a \leadsto^{+} a_{n+1}$. The induction step proceeds
by recurring on $a_{n+1}$, which steps to $a_{n+2}$. This has the effect
of following the infinite chain of reductions, leading to a divergence.
We can extract the proof of false by applying this induction to the
step $a_0 \leadsto a_1$ of the sequence.

```agda
strongly-normalising→terminating : is-strongly-normalising _↝_ → is-terminating _↝_
strongly-normalising→terminating {_↝_ = _↝_} sn ∥chain∥ =
  ∥-∥-proj! $ do
    (aₙ , step) ← ∥chain∥
    inc $ Wf-induction _ sn
      (λ a → ∀ n → ¬ Trans _↝_ a (aₙ (suc n)))
      (λ a ih n aᵢ↝aₙ₊₁ → ih (aₙ (suc n)) aᵢ↝aₙ₊₁ (suc n) (step (suc n)))
      (aₙ 0) 0 (step zero)
```

<!-- [TODO: Reed M, 02/06/2023] Prove that they are equivalent if we assume LEM. -->

We can use the prior fact to show that strongly normalising rewrite
systems contain no loops, by using the constant sequence $a \leadsto a$
as our infinite chain.

```agda
strongly-normalising→acyclic
  : ∀ {A : Type ℓ} {_↝_ : A → A → Type ℓ'}
  → is-strongly-normalising _↝_
  → ¬ (∃[ a ∈ A ] (Trans _↝_ a a))
strongly-normalising→acyclic sn ∥loop∥ =
  strongly-normalising→terminating sn $
    ∥-∥-map (λ (a , a↝a) → (λ _ → a) , λ n → a↝a) ∥loop∥
```
