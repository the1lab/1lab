<!--
```agda
open import Cat.Prelude

open import Data.Sum.Base

open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Lattice
open import Order.Base

import Order.Lattice.Reasoning as Lat
import Order.Reasoning as Pos
```
-->

```agda
module Order.Lattice.Distributive {o ℓ} {P : Poset o ℓ} (l : is-lattice P) where
```

<!--
```agda
open Pos P
open Lat l
```
-->

# Distributive lattices {defines="distributive-lattice"}

A **distributive lattice**, as the name implies, is a [[lattice]] where
the operations of [[meet]] and [[join]] distribute over _each other_:
that is, for any triple of elements $x, y, z$,

$$
\begin{align*}
x \cap (y \cup z)& = (x \cap y) \cup (x \cap z) \\
x \cup (y \cap z)& = (x \cup y) \cap (x \cup z)\text{.}
\end{align*}
$$

Rather remarkably, it turns out that either equation implies the other.
We provide a pair of parametrised modules which quantifies over one of
the equations and proves the other. For convenience, these modules also
define distributivity _on the right_, too; this is a consequence of both
meets and joins being commutative operators.

<!--
```agda
module Distributive where
```
-->

```agda
  module from-∩ (∩-distribl : ∀ {x y z} → x ∩ (y ∪ z) ≡ (x ∩ y) ∪ (x ∩ z)) where abstract
    ∩-distribr : ∀ {x y z} → (y ∪ z) ∩ x ≡ (y ∩ x) ∪ (z ∩ x)
    ∩-distribr = ∩-comm ·· ∩-distribl ·· ap₂ _∪_ ∩-comm ∩-comm

    ∪-distribl : ∀ {x y z} → x ∪ (y ∩ z) ≡ (x ∪ y) ∩ (x ∪ z)
    ∪-distribl {x} {y} {z} = sym $
      (x ∪ y) ∩ (x ∪ z)             ≡⟨ ∩-distribl ⟩
      ((x ∪ y) ∩ x) ∪ ((x ∪ y) ∩ z) ≡⟨ ap₂ _∪_ ∩-absorbr refl ⟩
      x ∪ ((x ∪ y) ∩ z)             ≡⟨ ap₂ _∪_ refl ∩-distribr ⟩
      x ∪ (x ∩ z ∪ y ∩ z)           ≡⟨ ∪-assoc ⟩
      (x ∪ x ∩ z) ∪ (y ∩ z)         ≡⟨ ap₂ _∪_ ∪-absorbl refl ⟩
      x ∪ (y ∩ z)                   ∎

    ∪-distribr : ∀ {x y z} → (y ∩ z) ∪ x ≡ (y ∪ x) ∩ (z ∪ x)
    ∪-distribr = ∪-comm ·· ∪-distribl ·· ap₂ _∩_ ∪-comm ∪-comm
```

<details>
<summary>The construction assuming that join distributes over meet is
formally dual.</summary>

```agda
  module from-∪ (∪-distribl : ∀ {x y z} → x ∪ (y ∩ z) ≡ (x ∪ y) ∩ (x ∪ z)) where abstract
    ∪-distribr : ∀ {x y z} → (y ∩ z) ∪ x ≡ (y ∪ x) ∩ (z ∪ x)
    ∪-distribr = ∪-comm ·· ∪-distribl ·· ap₂ _∩_ ∪-comm ∪-comm

    ∩-distribl : ∀ {x y z} → x ∩ (y ∪ z) ≡ (x ∩ y) ∪ (x ∩ z)
    ∩-distribl {x} {y} {z} = sym $
      (x ∩ y) ∪ (x ∩ z)             ≡⟨ ∪-distribl ⟩
      ((x ∩ y) ∪ x) ∩ ((x ∩ y) ∪ z) ≡⟨ ap₂ _∩_ ∪-absorbr refl ⟩
      x ∩ ((x ∩ y) ∪ z)             ≡⟨ ap₂ _∩_ refl ∪-distribr ⟩
      x ∩ (x ∪ z) ∩ (y ∪ z)         ≡⟨ ∩-assoc ⟩
      (x ∩ (x ∪ z)) ∩ (y ∪ z)       ≡⟨ ap₂ _∩_ ∩-absorbl refl ⟩
      x ∩ (y ∪ z)                   ∎

    ∩-distribr : ∀ {x y z} → (y ∪ z) ∩ x ≡ (y ∩ x) ∪ (z ∩ x)
    ∩-distribr = ∩-comm ·· ∩-distribl ·· ap₂ _∪_ ∩-comm ∩-comm
```

</details>

As a further weakening of the preconditions, it turns out that it
suffices for distributivity to hold as an *in*equality, in the direction

$$
x \cap (y \cup z) \le (x \cap y) \cup (x \cap z)\text{,}
$$

since the other direction _always_ holds in a lattice.

```agda
distrib-le→∩-distribl
  : (∀ {x y z} → x ∩ (y ∪ z) ≤ (x ∩ y) ∪ (x ∩ z))
  → ∀ {x y z} → x ∩ (y ∪ z) ≡ (x ∩ y) ∪ (x ∩ z)
distrib-le→∩-distribl ∩-∪-distrib≤ = ≤-antisym ∩-∪-distrib≤ ∪-∩-distribl-≤
```
