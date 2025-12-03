---
description: |
  Directed sets.
---

<!--
```agda
open import Cat.Prelude

open import Data.Fin.Finite
open import Data.Fin.Base using (Fin; fzero; fsuc; fin-cons)

open import Order.Semilattice.Join
open import Order.Semilattice.Meet
open import Order.Base
```
-->

```agda
module Order.Directed where
```

# Directed sets

:::{.definition #upwards-directed-set}
A [[poset]] $P$ is **upwards directed** if it is [[merely]] inhabited
and every pair of elements $x, y : P$ merely has a (not necessarily least)
upper bound.
:::

```agda
record is-upwards-directed {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Poset P
  field
    inhab : ∥ Ob ∥
    upper-bound : ∀ x y → ∃[ z ∈ Ob ] (x ≤ z × y ≤ z)
```

If $P$ is upwards directed, then there merely exists an upper bound of
every [[finite]] subset of $P$.

```agda
  fin-upper-bound
    : ∀ {n}
    → (xᵢ : Fin n → Ob)
    → ∃[ y ∈ Ob ] (∀ ix → xᵢ ix ≤ y)
  fin-upper-bound {zero} xᵢ = do
    y ← inhab
    inc (y , (λ ()))
  fin-upper-bound {suc n} xᵢ = do
    (y , xᵢ≤y) ← fin-upper-bound (xᵢ ⊙ fsuc)
    (ub , x₀≤ub , y≤ub) ← upper-bound (xᵢ 0) y
    pure (ub , fin-cons x₀≤ub λ ix → ≤-trans (xᵢ≤y ix) y≤ub)
```

<!--
```agda
  finite-upper-bound
    : ∀ {κ} {Ix : Type κ}
    → ⦃ _ : Finite Ix ⦄
    → (xᵢ : Ix → Ob)
    → ∃[ y ∈ Ob ] (∀ ix → xᵢ ix ≤ y)
  finite-upper-bound ⦃ Ix-fin ⦄ xᵢ = do
    ix-eqv ← enumeration ⦃ Ix-fin ⦄
    (ub , xᵢ≤ub) ← fin-upper-bound (xᵢ ⊙ Equiv.from ix-eqv)
    inc (ub , λ ix → subst (λ ix → xᵢ ix ≤ ub) (Equiv.η ix-eqv ix) (xᵢ≤ub (Equiv.to ix-eqv ix)))
```
-->

<!--
```agda
{-# INLINE is-upwards-directed.constructor #-}

unquoteDecl H-Level-is-upwards-directed =
  declare-record-hlevel 1 H-Level-is-upwards-directed (quote is-upwards-directed)
```
-->

Every [[join semilattice]] is upwards directed.

```agda
is-join-slat→is-upwards-directed
  : ∀ {o ℓ} {L : Poset o ℓ}
  → is-join-semilattice L
  → is-upwards-directed L
{-# INLINE is-join-slat→is-upwards-directed #-}
is-join-slat→is-upwards-directed {L = L} L-slat = record
  { inhab = inc bot
  ; upper-bound = λ x y → inc (x ∪ y , l≤∪ , r≤∪)
  }
  where
    open Poset L
    open is-join-semilattice L-slat
```

:::{.definition #downwards-directed-set}
Dually, a [[poset]] $P$ is **downwards directed** if it is [[merely]] inhabited
and every pair of elements $x, y : P$ merely has a (not necessarily least)
lower bound.
:::


```agda
record is-downwards-directed {o ℓ} (P : Poset o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Poset P
  field
    inhab : ∥ Ob ∥
    lower-bound : ∀ x y → ∃[ z ∈ Ob ] (z ≤ x × z ≤ y)
```

If $P$ is downward directed, then every finite subset $S \subseteq P$
have a (not necessarily greatest) lower bound.

```agda
  fin-lower-bound
    : ∀ {n}
    → (xᵢ : Fin n → Ob)
    → ∃[ y ∈ Ob ] (∀ ix → y ≤ xᵢ ix)
```

<details>
<summary>The proof is formally dual to the upwards directed case, so we omit it.
</summary>

```agda
  fin-lower-bound {zero} xᵢ = do
    y ← inhab
    inc (y , (λ ()))
  fin-lower-bound {suc n} xᵢ = do
    (y , y≤xᵢ) ← fin-lower-bound (xᵢ ⊙ fsuc)
    (lb , lb≤x₀ , lb≤y) ← lower-bound (xᵢ 0) y
    pure (lb , fin-cons lb≤x₀ λ ix → ≤-trans lb≤y (y≤xᵢ ix))
```
</details>

<!--
```agda
  finite-lower-bound
    : ∀ {κ} {Ix : Type κ}
    → ⦃ _ : Finite Ix ⦄
    → (xᵢ : Ix → Ob)
    → ∃[ y ∈ Ob ] (∀ ix → y ≤ xᵢ ix)
  finite-lower-bound ⦃ Ix-fin ⦄ xᵢ = do
    ix-eqv ← enumeration ⦃ Ix-fin ⦄
    (lb , lb≤xᵢ) ← fin-lower-bound (xᵢ ⊙ Equiv.from ix-eqv)
    inc (lb , λ ix → subst (λ ix → lb ≤ xᵢ ix) (Equiv.η ix-eqv ix) (lb≤xᵢ (Equiv.to ix-eqv ix)))
```
-->

<!--
```agda
{-# INLINE is-downwards-directed.constructor #-}

unquoteDecl H-Level-is-downwards-directed =
  declare-record-hlevel 1 H-Level-is-downwards-directed (quote is-downwards-directed)
```
-->

Every [[meet semilattice]] is downwards directed.

```agda
is-meet-slat→is-downwards-directed
  : ∀ {o ℓ} {L : Poset o ℓ}
  → is-meet-semilattice L
  → is-downwards-directed L
{-# INLINE is-meet-slat→is-downwards-directed #-}
is-meet-slat→is-downwards-directed {L = L} L-slat = record
  { inhab = inc top
  ; lower-bound = λ x y → inc (x ∩ y , ∩≤l , ∩≤r)
  }
  where
    open Poset L
    open is-meet-semilattice L-slat
```
