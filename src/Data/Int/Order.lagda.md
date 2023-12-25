<!--
```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Data.Int.Properties
open import Data.Int.Base
open import Data.Dec

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Data.Int.Order where
```

# Ordering integers {defines="ordering-on-integers"}

The usual [[partial order]] on the integers relies on the observation
that the number line looks like two copies of the natural numbers,
smashed end-to-end at the number zero. This is precisely the definition
of the order we use:

```agda
data _≤_ : Int → Int → Type where
  neg≤neg : ∀ {x y} → y Nat.≤ x → negsuc x ≤ negsuc y
  pos≤pos : ∀ {x y} → x Nat.≤ y → pos x    ≤ pos y
  neg≤pos : ∀ {x y}             → negsuc x ≤ pos y
```

Note the key properties: the ordering between negative numbers is
reversed, and every negative number is smaller than every positive
number.  This means that $\bZ$ decomposes, as an order, into an _ordinal
sum_ $\bN\op + \bN$.

## Basic properties

Proving that this is actually a partial order is a straightforward
combination of case-bashing and appealing to the analogous properties
for the ordering on natural numbers.

```agda
¬pos≤neg : ∀ {x y} → pos x ≤ negsuc y → ⊥
¬pos≤neg ()

≤-is-prop : ∀ {x y} → is-prop (x ≤ y)
≤-is-prop (neg≤neg p) (neg≤neg q) = ap neg≤neg (Nat.≤-is-prop p q)
≤-is-prop (pos≤pos p) (pos≤pos q) = ap pos≤pos (Nat.≤-is-prop p q)
≤-is-prop neg≤pos neg≤pos = refl

≤-refl : ∀ {x} → x ≤ x
≤-refl {x = pos x}    = pos≤pos Nat.≤-refl
≤-refl {x = negsuc x} = neg≤neg Nat.≤-refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans (neg≤neg p) (neg≤neg q) = neg≤neg (Nat.≤-trans q p)
≤-trans (neg≤neg p) neg≤pos     = neg≤pos
≤-trans (pos≤pos p) (pos≤pos q) = pos≤pos (Nat.≤-trans p q)
≤-trans neg≤pos (pos≤pos x)     = neg≤pos

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym (neg≤neg p) (neg≤neg q) = ap negsuc (Nat.≤-antisym q p)
≤-antisym (pos≤pos p) (pos≤pos q) = ap pos (Nat.≤-antisym p q)
```

## Totality

The ordering on the integers is [[decidable]], and moreover it is a
[[total order]]. We show _weak totality_: if $x \not\le y$, then $y \le
x$.

```agda
≤-is-weakly-total : ∀ x y → ¬ (x ≤ y) → y ≤ x
≤-is-weakly-total (pos    x) (pos    y) p = pos≤pos $
  Nat.≤-is-weakly-total x y (p ∘ pos≤pos)
≤-is-weakly-total (pos    x) (negsuc y) p = neg≤pos
≤-is-weakly-total (negsuc x) (pos    y) p = absurd (p neg≤pos)
≤-is-weakly-total (negsuc x) (negsuc y) p = neg≤neg $
  Nat.≤-is-weakly-total y x (p ∘ neg≤neg)

instance
  Dec-≤ : ∀ {x y} → Dec (x ≤ y)
  Dec-≤ {pos x} {pos y} with holds? (x Nat.≤ y)
  ... | yes p = yes (pos≤pos p)
  ... | no ¬p = no λ { (pos≤pos p) → ¬p p }
  Dec-≤ {negsuc x} {negsuc y} with holds? (y Nat.≤ x)
  ... | yes p = yes (neg≤neg p)
  ... | no ¬p = no λ { (neg≤neg p) → ¬p p }
  Dec-≤ {pos x} {negsuc y} = no ¬pos≤neg
  Dec-≤ {negsuc x} {pos y} = yes neg≤pos
```

<!--
```agda
  H-Level-≤ : ∀ {n x y} → H-Level (x ≤ y) (suc n)
  H-Level-≤ = prop-instance ≤-is-prop
```
-->

## Compatibility with the structure

The last case bash in this module will establish that the ordering on
natural numbers is compatible with the successor equivalence. Since
addition is iterated application of this equivalence, we get as a
corollary that addition also respects the order.

```agda
suc-≤ : ∀ x y → x ≤ y → sucℤ x ≤ sucℤ y
suc-≤ (pos x) (pos y) (pos≤pos p) = pos≤pos (Nat.s≤s p)
suc-≤ (negsuc zero) (pos y) p = pos≤pos Nat.0≤x
suc-≤ (negsuc zero) (negsuc zero) p = ≤-refl
suc-≤ (negsuc zero) (negsuc (suc y)) (neg≤neg ())
suc-≤ (negsuc (suc x)) (pos y) p = neg≤pos
suc-≤ (negsuc (suc x)) (negsuc zero) p = neg≤pos
suc-≤ (negsuc (suc x)) (negsuc (suc y)) (neg≤neg (Nat.s≤s p)) = neg≤neg p

pred-≤ : ∀ x y → x ≤ y → predℤ x ≤ predℤ y
pred-≤ posz posz p = ≤-refl
pred-≤ posz (possuc y) p = neg≤pos
pred-≤ (possuc x) posz (pos≤pos ())
pred-≤ (possuc x) (possuc y) (pos≤pos (Nat.s≤s p)) = pos≤pos p
pred-≤ (negsuc x) posz p = neg≤neg Nat.0≤x
pred-≤ (negsuc x) (possuc y) p = neg≤pos
pred-≤ (negsuc x) (negsuc y) (neg≤neg p) = neg≤neg (Nat.s≤s p)

rotℤ≤l : ∀ k x y → x ≤ y → rotℤ k x ≤ rotℤ k y
rotℤ≤l posz             x y p = p
rotℤ≤l (possuc k)       x y p = suc-≤ _ _ (rotℤ≤l (pos k) x y p)
rotℤ≤l (negsuc zero)    x y p = pred-≤ _ _ p
rotℤ≤l (negsuc (suc k)) x y p = pred-≤ _ _ (rotℤ≤l (negsuc k) x y p)

abstract
  +ℤ-mono-l : ∀ k x y → x ≤ y → (k +ℤ x) ≤ (k +ℤ y)
  +ℤ-mono-l k x y p = transport
    (sym (ap₂ _≤_ (rot-is-add k x) (rot-is-add k y)))
    (rotℤ≤l k x y p)

  +ℤ-mono-r : ∀ k x y → x ≤ y → (x +ℤ k) ≤ (y +ℤ k)
  +ℤ-mono-r k x y p = transport
    (ap₂ _≤_ (+ℤ-commutative k x) (+ℤ-commutative k y))
    (+ℤ-mono-l k x y p)
```
