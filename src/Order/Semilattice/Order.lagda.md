```agda
open import Order.Semilattice
open import Order.Diagram.Glb
open import Order.Base

open import Cat.Prelude

import Order.Reasoning as Poset

module Order.Semilattice.Order where
```

# Semilattices from posets

We have already established that [semilattices], which we define
algebraically, have an underlying [poset]. The aim of this module is to
prove the converse: If you have a poset $(A, \le)$ such that any finite
number of elements has a greatest lower bound, then $A$ is a
semilattice. As usual, by induction, it suffices to have nullary and
binary greatest lower bounds: A top element, and meets.

[semilattices]: Order.Semilattices.html
[poset]: Order.Base.html

```agda
poset→semilattice
  : ∀ {ℓₒ ℓᵣ} {T : Type ℓₒ} (P : Poset ℓₒ ℓᵣ)
    (meet : ∀ x y → Σ _ (is-meet P x y))
    (top : ⌞ P ⌟)
    (is-top : ∀ x → Poset._≤_ P x top)
  → Semilattice-on ⌞ P ⌟

poset→semilattice P meet top is-top = to-semilattice-on make-p where
  module P = Poset P
  module ml = make-semilattice
  open is-meet

  _∩_ : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
  x ∩ y = meet x y .fst

  module meet {x} {y} = is-meet (meet x y .snd) renaming (meet≤l to l ; meet≤r to r)

  make-p : make-semilattice ⌞ P ⌟
  make-p .ml.has-is-set = hlevel!
  make-p .ml.top = top
  make-p .ml.op = _∩_
  make-p .ml.idl = P.≤-antisym meet.r (meet.greatest _ (is-top _) P.≤-refl)
  make-p .ml.associative = P.≤-antisym
    (meet.greatest _
      (meet.greatest _ meet.l (P.≤-trans meet.r meet.l))
      (P.≤-trans meet.r meet.r))
    (meet.greatest _
      (P.≤-trans meet.l meet.l)
      (meet.greatest _ (P.≤-trans meet.l meet.r) meet.r))
  make-p .ml.commutative = P.≤-antisym
    (meet.greatest _ meet.r meet.l)
    (meet.greatest _ meet.r meet.l)
  make-p .ml.idempotent = P.≤-antisym meet.l (meet.greatest _ P.≤-refl P.≤-refl)
```
