<!--
```agda
open import Cat.Prelude

open import Data.Sum.Base

open import Order.Lattice.Distributive
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Diagram.Top
open import Order.Lattice
open import Order.Base

import Order.Diagram.Join.Reasoning as Joins
import Order.Diagram.Meet.Reasoning as Meets
import Order.Lattice.Reasoning as Lat
import Order.Reasoning as Pos
```
-->

```agda
module Order.Heyting where
```

# Heyting algebras {defines="heyting-algebra"}

A **Heyting algebra** is a [[lattice]] which is equipped to handle
**implication**: it has a binary operation $a \heyt b$ for which we have
an equivalence between $(a \land b) \le c$ and $a \le (b \heyt c)$.
Reading this from the perspective of logic, we may interpret the
parameter $a$ as a *context*, so that our equivalence says we have
inference rules

::: mathpar
$$ \frac{a, b \vdash c}{a \vdash b \heyt c} $$

$$ \frac{a \vdash b \heyt c}{a, b \vdash c} $$
:::

When we enrich our [[poset]] of propositions to a [[category]] of
contexts, the notion of Heyting algebra is generalised to that of
[[Cartesian closed category|cartesian closed]] (with [[finite
coproducts|coproduct]]).

```agda
record is-heyting-algebra {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  open Poset P

  field
    has-top    : Top P
    has-bottom : Bottom P

    _∪_      : Ob → Ob → Ob
    ∪-joins  : ∀ x y → is-join P x y (x ∪ y)

    _∩_      : Ob → Ob → Ob
    ∩-meets  : ∀ x y → is-meet P x y (x ∩ y)

    _⇨_  : ⌞ P ⌟ → ⌞ P ⌟ → ⌞ P ⌟
    ƛ    : ∀ {x y z} → x ∩ y ≤ z → x ≤ y ⇨ z
    ev   : ∀ {x y z} → x ≤ y ⇨ z → x ∩ y ≤ z
```

<!--
```agda
  infixr 23 _⇨_
  infixr 24 _∪_
  infixr 25 _∩_

  has-is-lattice : is-lattice P
  has-is-lattice .is-lattice.has-bottom = has-bottom
  has-is-lattice .is-lattice.has-top    = has-top
  has-is-lattice .is-lattice._∩_        = _∩_
  has-is-lattice .is-lattice.∩-meets    = ∩-meets
  has-is-lattice .is-lattice._∪_        = _∪_
  has-is-lattice .is-lattice.∪-joins    = ∪-joins
```
-->

## Elementary properties

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} (heyt : is-heyting-algebra P) where
  open is-heyting-algebra heyt
  open Lat has-is-lattice hiding (_∪_ ; _∩_)
  open Pos P
```
-->

The first thing we note about Heyting algebras is that they are
[[distributive lattices]]. This is because, for an arbitrary $P$, we can
reduce the problem of showing

$$
x \cap (y \cup z) \le P \text{,}
$$

by adjointness, to showing

$$
(y \cup z) \le x \heyt P \text{,}
$$

where the universal property of the join is actually applicable ---
allowing us further reductions to showing showing $(y \land x) \le P$
and $(z \land x) \le P$. The following calculation formalises this
sketch:

```agda
  ∩-∪-distrib≤ : ∀ {x y z} → x ∩ (y ∪ z) ≤ (x ∩ y) ∪ (x ∩ z)
  ∩-∪-distrib≤ {x} {y} {z} =
    let
      case₁ : y ∩ x ≤ (x ∩ y) ∪ (x ∩ z)
      case₁ = ≤-trans (≤-refl' ∩-comm) l≤∪

      case₂ : z ∩ x ≤ (x ∩ y) ∪ (x ∩ z)
      case₂ = ≤-trans (≤-refl' ∩-comm) r≤∪

      body : (y ∪ z) ≤ x ⇨ (x ∩ y) ∪ (x ∩ z)
      body = ∪-universal _ (ƛ case₁) (ƛ case₂)
    in x ∩ (y ∪ z)    =⟨ ∩-comm ⟩
       (y ∪ z) ∩ x    ≤⟨ ev body ⟩
       x ∩ y ∪ x ∩ z  ≤∎
```

<!--
```agda
  ∩-distribl : ∀ {x y z} → x ∩ (y ∪ z) ≡ (x ∩ y) ∪ (x ∩ z)
  ∩-distribl = distrib-le→∩-distribl has-is-lattice ∩-∪-distrib≤

  open Distributive.from-∩ has-is-lattice ∩-distribl
```
-->
