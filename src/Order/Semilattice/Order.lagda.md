```agda
open import Cat.Prelude

open import Order.Diagram.Glb
open import Order.Semilattice
open import Order.Base

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

[semilattices]: Order.Semilattice.html
[poset]: Order.Base.html

To this end, we define a type of finitely complete posets: Posets
possessing meets and a top element.

```agda
record Finitely-complete-poset ℓₒ ℓᵣ : Type (lsuc (ℓₒ ⊔ ℓᵣ)) where
  no-eta-equality
  field
    poset : Poset ℓₒ ℓᵣ
    _∩_         : ⌞ poset ⌟ → ⌞ poset ⌟ → ⌞ poset ⌟
    has-is-meet : ∀ {x y} → is-meet poset x y (x ∩ y)

    top        : ⌞ poset ⌟
    has-is-top : ∀ {x} → Poset._≤_ poset x top

  open Poset poset public
  private module meet {x} {y} = is-meet (has-is-meet {x} {y})
  open meet renaming (meet≤l to ∩≤l ; meet≤r to ∩≤r ; greatest to ∩-univ) public

  le→meet : ∀ {x y} → x ≤ y → x ≡ x ∩ y
  le→meet x≤y = le-meet poset x≤y has-is-meet

  meet→le : ∀ {x y} → x ≡ x ∩ y → x ≤ y
  meet→le {y = y} x=x∩y = subst (_≤ y) (sym x=x∩y) ∩≤r
```

From a finitely complete poset, we can define a semilattice: from the
universal property of meets, we can conclude that they are associative,
idempotent, commutative, and have the top element as a unit.

```agda
fc-poset→semilattice : ∀ {o ℓ} (P : Finitely-complete-poset o ℓ) → Semilattice o
fc-poset→semilattice P = to-semilattice make-p where
  module ml = make-semilattice
  open Finitely-complete-poset P

  make-p : make-semilattice ⌞ poset ⌟
  make-p .ml.has-is-set = hlevel!
  make-p .ml.top = top
  make-p .ml.op = _∩_
  make-p .ml.idl = ≤-antisym ∩≤r (∩-univ _ has-is-top ≤-refl)
  make-p .ml.associative = ≤-antisym
    (∩-univ _
      (∩-univ _ ∩≤l (≤-trans ∩≤r ∩≤l))
      (≤-trans ∩≤r ∩≤r))
    (∩-univ _ (≤-trans ∩≤l ∩≤l) (∩-univ _ (≤-trans ∩≤l ∩≤r) ∩≤r))
  make-p .ml.commutative = ≤-antisym
    (∩-univ _ ∩≤r ∩≤l)
    (∩-univ _ ∩≤r ∩≤l)
  make-p .ml.idempotent = ≤-antisym ∩≤l (∩-univ _ ≤-refl ≤-refl)
```

It's a general fact about meets that the semilattice ordering defined
with the meets from a finitely complete poset agrees with our original
ordering, which we link below:

```agda
_ = le-meet
```
