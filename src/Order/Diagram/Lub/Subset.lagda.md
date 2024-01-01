<!--
```agda
open import Cat.Prelude

open import Order.Diagram.Lub
open import Order.Base

import Order.Diagram.Lub.Reasoning as Lubs
import Order.Reasoning
```
-->

```agda
module Order.Diagram.Lub.Subset where
```

# Joins of subsets

Imagine you have a [[poset]] $A$ whose carrier has size $\kappa$, which
furthermore has [[least upper bounds]] for $\kappa$-small families of
elements. But imagine that you have a second universe $\lambda$, and you
have a $\lambda$-small predicate $P : \bb{P}_{\lambda}(A)$. Normally,
you'd be out of luck: there is no reason for $A$ to admit $(\kappa
\sqcup \lambda)$-sized joins.

But since we've assumed [[propositional resizing]], we can resize
(pointwise) $P$ to be valued in the universe $\kappa$; That way we can
turn the total space $\int P$ into a $\kappa$-small type! By projecting
the first component, we have a $\kappa$-small family of elements, which
has a join. This is a good definition for the **join of the subset
$P$**.

```agda
module _ {o ℓ} (F : Poset o ℓ) (cocompl : ∀ {I : Type o} (f : I → ⌞ F ⌟) → Lub F f) where
  open Order.Reasoning F
  private module P = Lubs.Lubs F cocompl

  subset-cup : ∀ {ℓ'} (P : ⌞ F ⌟ → Prop ℓ') → ⌞ F ⌟
  subset-cup P = P.⋃ {I = Σ[ t ∈ ⌞ F ⌟ ] □ (t ∈ P)} fst

  subset-cup-colimiting
    : ∀ {ℓ'} (P : ⌞ F ⌟ → Prop ℓ') {x}
    → x ∈ P → x ≤ subset-cup P
  subset-cup-colimiting P x = P.⋃-inj (_ , (inc x))

  subset-cup-universal
    : ∀ {ℓ'} (P : ⌞ F ⌟ → Prop ℓ') {x}
    → (∀ i → i ∈ P → i ≤ x)
    → subset-cup P ≤ x
  subset-cup-universal P f = P.⋃-universal _ λ (i , w) → f i (out! w)
```

Keep imagining that you have a subset $P \sube A$: Can we construct a
meet for it? Yes! By taking the join of all possible upper bounds for
$P$, we get the a lower bound among upper bounds of $P$: a meet for $P$.

```agda
  subset-cap : ∀ {ℓ'} (P : ⌞ F ⌟ → Prop ℓ') → ⌞ F ⌟
  subset-cap P = subset-cup λ x → el! (∀ a → ∣ P a ∣ → x ≤ a)

  subset-cap-limiting
    : ∀ {ℓ'} (P : ⌞ F ⌟ → Prop ℓ') {x} → x ∈ P → subset-cap P ≤ x
  subset-cap-limiting P x∈P =
    subset-cup-universal (λ x → el _ hlevel!) λ i a∈P→i≤a → a∈P→i≤a _ x∈P

  subset-cap-universal
    : ∀ {ℓ} (P : ⌞ F ⌟ → Prop ℓ) {x}
    → (∀ i → i ∈ P → x ≤ i)
    → x ≤ subset-cap P
  subset-cap-universal P x∈P = subset-cup-colimiting (λ _ → el _ hlevel!) x∈P
```
