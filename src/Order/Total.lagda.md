<!--
```agda
open import 1Lab.Prelude

open import Data.Dec
open import Data.Sum

open import Homotopy.Pushout
open import Homotopy.Join

open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Base
```
-->

```agda
module Order.Total where
```

<!--
```agda
open is-join
open is-meet
```
-->

# Total orders {defines="total-order"}

A **total order** is a [[partial order]] where every pair of elements
can be compared.

```agda
record is-total-order {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  open Poset P public

  field
    compare : ∀ x y → (x ≤ y) ∗ (y ≤ x)
```

<!--
```agda
private unquoteDecl is-total-order-eqv = declare-record-iso is-total-order-eqv (quote is-total-order)

instance
  H-Level-is-total-order : ∀ {o ℓ} {P : Poset o ℓ} {k} → H-Level (is-total-order P) (suc k)
  H-Level-is-total-order = prop-instance (Iso→is-hlevel 1 is-total-order-eqv
    (Π-is-hlevel² 1 λ _ _ → join-is-prop (hlevel 1) (hlevel 1)))
```
-->

::: note
The _ordering_ procedure, `compare`{.Agda}, is orthogonal from having a
[[decision procedure|decidable]] for the order: if comparing $x, y$
results in $x \le y$, we can not, in general, turn this into a proof of
$y \not\le x$.
:::

Having a decision procedure for the relative order of two elements
allows us to compute [[meets]] and [[joins]] in a very straightforward
way: We test whether $x \le y$, and, if that's the case, then $\min(x,y)
= x$; otherwise, $\min(x,y) = y$. The definition of $\max$ is exactly
dual.

<!--
```agda
module minmax {o ℓ} {P : Poset o ℓ} (to : is-total-order P) where
  open is-total-order to
```
-->

```agda
  min : (x y : ⌞ P ⌟) → ⌞ P ⌟
  min x y = worker (compare x y) module min where
    worker = Pushout-elim (λ _ → x) (λ _ → y)
      (λ (x≤y , y≤x) → ≤-antisym x≤y y≤x)
```

The proofs that this is actually the meet of $x$ and $y$ proceed by
doing the comparison again: this "unblocks" the computation of $\min$.

```agda
  abstract
    min-≤l : ∀ x y → min x y ≤ x
    min-≤l x y = join-elim-prop
      {P = λ p → min.worker x y p ≤ x} (λ _ → hlevel 1)
      (λ _ → ≤-refl) (λ q → q) (compare x y)

    min-≤r : ∀ x y → min x y ≤ y
    min-≤r x y = join-elim-prop
      {P = λ p → min.worker x y p ≤ y} (λ _ → hlevel 1)
      (λ p → p) (λ _ → ≤-refl) (compare x y)

    min-univ : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
    min-univ x y z p q = join-elim-prop
      {P = λ p → z ≤ min.worker x y p} (λ _ → hlevel 1)
      (λ _ → p) (λ _ → q) (compare x y)
```

This is everything we need to prove that we have our hands on a meet.

```agda
  min-is-meet : ∀ x y → is-meet P x y (min x y)
  min-is-meet x y .meet≤l   = min-≤l x y
  min-is-meet x y .meet≤r   = min-≤r x y
  min-is-meet x y .greatest = min-univ x y
```

Since the case of maxima is precisely dual, we present it with no
further commentary.

```agda
  max : (x y : ⌞ P ⌟) → ⌞ P ⌟
  max x y = worker (compare x y) module max where
    worker = Pushout-elim (λ _ → y) (λ _ → x)
      (λ (x≤y , y≤x) → ≤-antisym y≤x x≤y)

  abstract
    max-≤l : ∀ x y → x ≤ max x y
    max-≤l x y = join-elim-prop
      {P = λ p → x ≤ max.worker x y p} (λ _ → hlevel 1)
      (λ p → p) (λ _ → ≤-refl) (compare x y)

    max-≤r : ∀ x y → y ≤ max x y
    max-≤r x y = join-elim-prop
      {P = λ p → y ≤ max.worker x y p} (λ _ → hlevel 1)
      (λ _ → ≤-refl) (λ q → q) (compare x y)

    max-univ : ∀ x y z → x ≤ z → y ≤ z → max x y ≤ z
    max-univ x y z p q = join-elim-prop
      {P = λ p → max.worker x y p ≤ z} (λ _ → hlevel 1)
      (λ _ → q) (λ _ → p) (compare x y)

  max-is-join : ∀ x y → is-join P x y (max x y)
  max-is-join x y .l≤join = max-≤l x y
  max-is-join x y .r≤join = max-≤r x y
  max-is-join x y .least  = max-univ x y
```

## Decidable total orders {defines="decidable-total-order"}

In particularly nice cases, we can not only decide the relative position
of a pair of elements, but whether a pair of elements is related at all:
this is a **decidable total order**.

<!--
```agda
is-decidable-poset : ∀ {o ℓ} (P : Poset o ℓ) → Type _
is-decidable-poset P = ∀ {x y} → Dec (x ≤ y)
  where open Poset P
```
-->

```agda
record is-decidable-total-order {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    has-is-total : is-total-order P

  open is-total-order has-is-total public
```

As the name implies, a decidable total order must be a total order; and
it must also be decidable:

```agda
  field
    ⦃ dec-≤    ⦄ : is-decidable-poset P
    ⦃ discrete ⦄ : Discrete ⌞ P ⌟
```

Note that we have included a requirement that a decidable total order be
[[discrete]], i.e., that its equality is also decidable. This is purely
for formalisation reasons --- allowing the user to specify a more
efficient decision procedure for equality ---, since we can use the
decidable ordering to decide equality.

```agda
  private
    was-discrete-anyways : Discrete ⌞ P ⌟
    was-discrete-anyways .decide x y with holds? (x ≤ y) | holds? (y ≤ x)
    ... | yes x≤y | yes y≤x = yes (≤-antisym x≤y y≤x)
    ... | yes x≤y | no ¬y≤x = no λ x=y → ¬y≤x (≤-refl' (sym x=y))
    ... | no ¬x≤y | _       = no λ x=y → ¬x≤y (≤-refl' x=y)
```

Note that, if we have a decidable order, then the requirement of
totality can be weakened to the property that, for any $x, y$, we have

$$
(x \not\le y) \to (y \le x)
$$,

which we refer to as **weak totality**.

<!--
```agda
  from-not-≤ : ∀ {x y} → ¬ (x ≤ y) → y ≤ x
  from-not-≤ {x} {y} ¬x≤y = join-elim-prop (λ _ → hlevel 1)
    (λ x≤y → absurd (¬x≤y x≤y)) (λ y≤x → y≤x) (compare x y)

module _ {o ℓ} {P : Poset o ℓ} ⦃ _ : Discrete ⌞ P ⌟ ⦄ ⦃ _ : is-decidable-poset P ⦄ where
  open Poset P
```
-->

```agda
  from-weakly-total
    : (wk : ∀ {x y} → ¬ (x ≤ y) → y ≤ x)
    → is-decidable-total-order P
  from-weakly-total wk = record { has-is-total = tot } where
```

The construction is straightforward: we can test whether $x \le y$, and
if it holds, we're done; Otherwise, weak totality lets us conclude that
$y \le x$ from the computed witness of $x \not\le y$.

```agda
    compare : ∀ x y → (x ≤ y) ∗ (y ≤ x)
    compare x y with holds? (x ≤ y)
    ... | yes x≤y = inl x≤y
    ... | no ¬x≤y = inr (wk ¬x≤y)

    tot : is-total-order P
    tot = record { compare = compare }
```
