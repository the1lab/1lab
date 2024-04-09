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

<!--
```agda
module
  Join-subsets
    {o ℓ} (F : Poset o ℓ)
    {⋃ : {I : Type o} (f : I → ⌞ F ⌟) → ⌞ F ⌟}
    (⋃-lubs : ∀ {I} f → is-lub F f (⋃ {I} f))
  where
  open Order.Reasoning F
  private module P = Lubs.Lubs F ⋃-lubs
```
-->

```agda
  opaque
    ⋃ˢ : ∀ (P : ⌞ F ⌟ → Ω) → ⌞ F ⌟
    ⋃ˢ P = ⋃ {I = Σ[ t ∈ F ] □ (t ∈ P)} fst

    ⋃ˢ-inj
      : ∀ {P : ⌞ F ⌟ → Ω} {x}
      → x ∈ P → x ≤ ⋃ˢ P
    ⋃ˢ-inj x = P.⋃-inj (_ , (inc x))

    ⋃ˢ-universal
      : ∀ {P : ⌞ F ⌟ → Ω} {x}
      → (∀ i → i ∈ P → i ≤ x)
      → ⋃ˢ P ≤ x
    ⋃ˢ-universal f = P.⋃-universal _ λ (i , w) → f i (□-out! w)
```
