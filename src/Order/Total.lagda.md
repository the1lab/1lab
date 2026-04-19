<!--
```agda
open import 1Lab.Prelude

open import Data.Bool
open import Data.Dec
open import Data.Sum

open import Homotopy.Space.Suspension.Properties
open import Homotopy.Space.Suspension
open import Homotopy.Pushout
open import Homotopy.Join

open import Meta.Invariant

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
can be compared: that is, in which we have $∀ x y.\ x ≤ y ∨ y ≤ x$.
Note the use of the [[disjunction]]: we want totality to be a proposition,
and having the truncation on the outside of the quantifiers would
actually yield a [[decidable total order]]!

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

Totality allows us to compute [[meets]] and [[joins]] in a very straightforward
way: in a poset, meets and joins are propositions (by antisymmetry), so we
can reason by cases. We test whether $x \le y$, and, if that's the case,
then $\min(x,y) = x$; otherwise, $\min(x,y) = y$. The definition of
$\max$ is exactly dual.

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

A total order that is also a [[decidable partial order]] is called a
**decidable total order**.

```agda
record is-decidable-total-order {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  field
    has-is-total : is-total-order P
    ⦃ dec-≤ ⦄    : is-decidable-poset P

  open is-total-order has-is-total public
```

Every decidable poset has decidable equality (see
`decidable→discrete`{.Agda}), but we include this as a redundant field
for formalisation reasons --- allowing the user to specify a more
efficient decision procedure for equality.

```agda
  field
    ⦃ discrete ⦄ : Discrete ⌞ P ⌟
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

unquoteDecl H-Level-is-decidable-total-order =
  declare-record-hlevel 1 H-Level-is-decidable-total-order (quote is-decidable-total-order)

module _ {o ℓ} (P : Poset o ℓ) (t : is-total-order P) (d : is-decidable-poset P) where
  mk-decidable-total-order : is-decidable-total-order P
  mk-decidable-total-order =
    record { has-is-total = t; dec-≤ = d; discrete = decidable→discrete P ⦃ d ⦄ }

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

### As discrete total orders

We now turn to some surprising restatements of the property of being a
decidable total order. For the purposes of this page, let's call a
partial order **strongly total** if there exists a function
with the type $∀ x y.\ x ≤ y ⊎ y ≤ x$: we remove the truncation from the
definition of a total order.^[Note that `is-strongly-total` is not a
proposition, since it carries at least a bit of data for each element.
The actual property it refers to is the *mere* existence of such a
function, but it is more convenient to talk about the untruncated
version.]

```agda
module _ {o ℓ} (P : Poset o ℓ) where
  open Poset P

  is-strongly-total : Type (o ⊔ ℓ)
  is-strongly-total = ∀ x y → x ≤ y ⊎ y ≤ x

  strongly-total→total : is-strongly-total → is-total-order P
  strongly-total→total st =
    record { compare = λ x y → [ inl , inr ] (st x y) }
```

We then have that *decidable* total orders, *discrete* total
orders,^[That is, total orders with decidable equality.] and *strong*
total orders are all the same thing! We already know that every
decidable total order is discrete, so we have to show that discrete
total orders are strong and that strong total orders are decidable.

For the first step, we proceed by cases: if $x = y$, then we can pick
either branch arbitrarily by reflexivity. Otherwise, we note that
$x ≤ y$ and $y ≤ x$ are *mutually exclusive* propositions by
antisymmetry, so their disjunction is already a proposition and we can
safely get rid of the truncation.

```agda
  discrete-total→strong : is-total-order P → Discrete ⌞ P ⌟ → is-strongly-total
  discrete-total→strong total d x y with d .decide x y
  ... | yes p = inl (≤-refl' p)
  ... | no ¬p = join-elim-prop
    (λ _ → disjoint-⊎-is-prop ≤-thin ≤-thin λ (x≤y , y≤x) → ¬p (≤-antisym x≤y y≤x))
    inl inr
    (compare x y)
    where open is-total-order total using (compare)
```

The fact that strong total orders are decidable is slightly more subtle:
in order to decide whether $x ≤ y$ or not, we proceed by cases on the
result of comparing the two pairs $(x, y)$ and $(y, x)$. If either of
those comparisons results in $x ≤ y$, then we can answer positively;
otherwise we have $y ≤ x$, and we observe that the first comparison must
have returned `inr` while the second must have returned `inl`. We thus
answer *negatively*: if we had $x ≤ y$, then by antisymmetry we would
have $x = y$, hence the two pairs would have yielded the same result.

```agda
  strong→decidable : is-strongly-total → is-decidable-poset P
  strong→decidable st {x} {y} with st x y in e₁ | st y x in e₂
  ... | inl x≤y | _       = yes x≤y
  ... | inr y≤x | inr x≤y = yes x≤y
  ... | inr y≤x | inl _   = no λ x≤y → true≠false $
    let p = ≤-antisym x≤y y≤x in
    true              ≡˘⟨ ap is-right (Id≃path.to e₁) ⟩
    is-right (st x y) ≡⟨ ap₂ (λ x y → is-right (st x y)) p (sym p) ⟩
    is-right (st y x) ≡⟨ ap is-right (Id≃path.to e₂) ⟩
    false             ∎
```

Thus all three properties are equivalent.

```agda
  strong→decidable-total
    : ∥ is-strongly-total ∥ → is-decidable-total-order P
  strong→decidable-total = rec! λ st →
    mk-decidable-total-order P (strongly-total→total st) (strong→decidable st)

  decidable-total→strong
    : is-total-order P → is-decidable-poset P → is-strongly-total
  decidable-total→strong total d =
    discrete-total→strong total (decidable→discrete P ⦃ d ⦄)

  discrete-total→decidable
    : is-total-order P → Discrete ⌞ P ⌟ → is-decidable-total-order P
  discrete-total→decidable total d =
    strong→decidable-total (inc (discrete-total→strong total d))
```

### A counterexample

We give a (Brouwerian) example of an undecidable total order: given a
proposition $P$, we construct a total order that if decidable if and
only if $P$ is.

The underlying set is the [[suspension]] of $P$, $\Susp{P}$.

```agda
module Latitude {ℓ} (P : Type ℓ) (P-prop : is-prop P) where
  ΣP = Susp P

  ΣP-is-set : is-set ΣP
  ΣP-is-set = Susp-prop-is-set P-prop
```

By declaring that the north pole is higher than the south pole, we
obtain a total order on $\Susp{P}$: we have $\mathsf{south} ≤
\mathsf{north}$ always, thus by antisymmetry $\mathsf{north} ≤
\mathsf{south}$ if and only if $P$.

```agda
  _≤_ : ΣP → ΣP → Prop ℓ
  _≤_ = Susp-elim _
    (Susp-elim _
      (el! (Lift _ ⊤)) -- N ≤ N
      (el P P-prop)    -- N ≤ S
      (λ p → n-ua (P→⊤≃P p)))
    (λ _ → el! (Lift _ ⊤)) -- S ≤ _
    (λ p → ext (Susp-elim-prop (λ _ → hlevel 1) refl (n-ua (P→⊤≃P p e⁻¹))))
    where
      P→⊤≃P : P → Lift _ ⊤ ≃ P
      P→⊤≃P p = is-contr→≃ (hlevel 0) (is-prop∙→is-contr P-prop p)
```

<details>
<summary>
It is straightforward but tedious to show that this is a total
order, so we omit the proofs.

```agda
  Latitude : Poset ℓ ℓ
  Latitude-total : is-total-order Latitude
```
</summary>

```agda
  ≤-refl : ∀ x → ∣ x ≤ x ∣
  ≤-refl = Susp-elim-prop (λ _ → hlevel 1) _ _

  ≤-trans : ∀ x y z → ∣ x ≤ y ∣ → ∣ y ≤ z ∣ → ∣ x ≤ z ∣
  ≤-trans = Susp-elim-prop (λ _ → hlevel 1)
    (Susp-elim-prop (λ _ → hlevel 1)
      (λ _ _ p → p)
      (Susp-elim-prop (λ _ → hlevel 1)
        _
        (λ p _ → p)))
    _

  ≤-antisym : ∀ x y → ∣ x ≤ y ∣ → ∣ y ≤ x ∣ → x ≡ y
  ≤-antisym = Susp-elim-prop
    (λ _ → Π-is-hlevel 1 λ _ → Π-is-hlevel² 1 λ _ _ → ΣP-is-set _ _)
    (Susp-elim-prop (λ _ → Π-is-hlevel² 1 λ _ _ → ΣP-is-set _ _)
      (λ _ _ → refl)
      (λ p _ → merid p))
    (Susp-elim-prop (λ _ → Π-is-hlevel² 1 λ _ _ → ΣP-is-set _ _)
      (λ _ p → sym (merid p))
      (λ _ _ → refl))

  Latitude .Poset.Ob = ΣP
  Latitude .Poset._≤_ x y = ∣ x ≤ y ∣
  Latitude .Poset.≤-thin {x} {y} = (x ≤ y) .is-tr
  Latitude .Poset.≤-refl {x} = ≤-refl x
  Latitude .Poset.≤-trans {x} {y} {z} = ≤-trans x y z
  Latitude .Poset.≤-antisym {x} {y} = ≤-antisym x y

  Latitude-total .is-total-order.compare = Susp-elim-prop
    (λ _ → Π-is-hlevel 1 λ _ → join-is-prop (hlevel 1) (hlevel 1))
    (Susp-elim-prop (λ _ → join-is-prop (hlevel 1) (hlevel 1))
      (inl _)
      (inr _))
    (λ _ → inl _)
```
</details>

By construction, this is a decidable order if and only if we can decide
$\mathsf{north} ≤ \mathsf{south}$, i.e. $P$.

```agda
  Latitude-decidable→P-decidable : is-decidable-poset Latitude → Dec P
  Latitude-decidable→P-decidable d = d {north} {south}
```
