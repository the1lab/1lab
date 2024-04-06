---
description: |
  Properties of the order on Fins.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Sum

import Data.Nat.Order
import Data.Nat.Base as Nat
```
-->
```agda
module Data.Fin.Order where
```

# Properties of the ordering on finite sets

We establish the basic properties of orders on finite sets.
These are properties of the order itself, and not how it interacts with
other structures on `Fin`{.Agda}.

<!--
```agda
private variable
  n m : Nat
```
-->

Recall that the order on `Fin`{.Agda} is given by the ordering on the underlying
natural number, so we can re-use most properties of the order on `Nat`{.Agda} verbatim.

```agda
open Data.Nat.Order hiding
  (<-below; ℕ-minimal-solution; ℕ-well-ordered; suc-wf; <-wf)
  public
```

However, this is not the case for *all* properties: in particular, higher-order properties
like `<-wf`{.Agda} and `<-below`{.Agda} cannot be directly re-used, as the nested
quantifiers range over all naturals, instead of all naturals smaller than some bound.

```agda
≤-bound : ∀ {i : ℕ< n} {j : Fin n} → (i .fst) Nat.≤ to-nat j → from-ℕ< i ≤ j
≤-bound {n = suc n} {i = zero , i<n} {j = j} i≤j = i≤j
≤-bound {n = suc n} {i = suc i , i<n} {j = fsuc j} i≤j = s≤s (≤-bound (≤-peel i≤j))

≤-unbound : ∀ {i : ℕ< n} {j : Fin n} → from-ℕ< i ≤ j → (i .fst) Nat.≤ to-nat j
≤-unbound {n = suc n} {i = zero , i<n} {j = j} i≤j = i≤j
≤-unbound {n = suc n} {i = suc i , i<n} {j = fsuc j} i≤j = s≤s (≤-unbound (≤-peel i≤j))

<-bound : ∀ {i : ℕ< n} {j : Fin n} → (i .fst) Nat.< to-nat j → from-ℕ< i < j
<-bound {n = suc n} {i = zero , i<n} {j = j} i<j = i<j
<-bound {n = suc n} {i = suc i , i<n} {j = fsuc j} i<j = s≤s (<-bound (≤-peel i<j))

<-unbound : ∀ {i : ℕ< n} {j : Fin n} → from-ℕ< i < j → (i .fst) Nat.< to-nat j
<-unbound {n = suc n} {i = zero , i<n} {j = j} i<j = i<j
<-unbound {n = suc n} {i = suc i , i<n} {j = fsuc j} i<j = s≤s (<-unbound (≤-peel i<j))
```

```agda
<-to-nat : ∀ (i : Fin n) → to-nat i Nat.< n
<-to-nat fzero = 0<s
<-to-nat (fsuc i) = Nat.s≤s (<-to-nat i)

<-below : ∀ {i j : Fin n} → (∀ k → k < i → k < j) → i ≤ j
<-below {n = suc n} {i} {j} p = Data.Nat.Order.<-below λ a a<i →
  <-unbound (p (from-ℕ< (a , (<-trans a<i (<-to-nat i)))) (<-bound a<i))
```

```agda
<-wf : ∀ {n} → Wf {A = Fin n} _<_
<-wf i = go i i ≤-refl where
  go : ∀ {m n} → (i : Fin m) → (j : Fin n) → .(to-nat i Nat.≤ to-nat j) → Acc _<_ i
  go fzero j i≤j = acc (λ k k<0 → absurd (x≮0 k<0))
  go (fsuc i) (fsuc j) i≤j = acc (λ k k<si → go k j (≤-trans (≤-peel k<si) (≤-peel i≤j)))
```
