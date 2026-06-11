<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Data.Int.Properties
open import Data.Bool.Base
open import Data.Int.Base
open import Data.Sum.Base
open import Data.Dec

import Data.Nat.Properties as Nat
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
_≤?_ : Int → Int → Bool
pos x    ≤? pos y    = x Nat.≤? y
pos x    ≤? negsuc y = false
negsuc x ≤? pos y    = true
negsuc x ≤? negsuc y = y Nat.≤? x

record _≤_ (x y : Int) : Type where
  constructor lift
  field
    lower : So (x ≤? y)
```

<!--
```agda
-- We need all this junk because we wrapped `So (x ≤? y)` in a record
-- which is definitionally injective in `x` and `y`.
abstract
  neg≤neg : ∀ {x y} → y Nat.≤ x → negsuc x ≤ negsuc y
  neg≤neg (Nat.lift y≤x) = lift y≤x

  pos≤pos : ∀ {x y} → x Nat.≤ y → pos x ≤ pos y
  pos≤pos (Nat.lift x≤y) = lift x≤y

  neg≤pos : ∀ {x y} → negsuc x ≤ pos y
  neg≤pos = lift oh

  unpos≤pos : ∀ {x y} → pos x ≤ pos y → x Nat.≤ y
  unpos≤pos (lift x≤y) = Nat.lift x≤y

  unneg≤neg : ∀ {x y} → negsuc x ≤ negsuc y → y Nat.≤ x
  unneg≤neg (lift y≤x) = Nat.lift y≤x
```
-->

<!--
```agda
instance
  ≤-neg-neg : ∀ {x y} ⦃ p : y Nat.≤ x ⦄ → negsuc x ≤ negsuc y
  ≤-neg-neg ⦃ p ⦄ = neg≤neg p

  ≤-pos-pos : ∀ {x y} ⦃ p : x Nat.≤ y ⦄ → pos x ≤ pos y
  ≤-pos-pos ⦃ p ⦄ = pos≤pos p

  ≤-neg-pos : ∀ {x y} → negsuc x ≤ pos y
  ≤-neg-pos = neg≤pos
```
-->

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
≤-is-prop _ _ = refl

≤-refl : ∀ {x} → x ≤ x
≤-refl {x = pos x}    = pos≤pos Nat.≤-refl
≤-refl {x = negsuc x} = neg≤neg Nat.≤-refl

≤-refl' : ∀ {x y} → x ≡ y → x ≤ y
≤-refl' {pos x} {pos y} p = pos≤pos (Nat.≤-refl' (pos-injective p))
≤-refl' {pos x} {negsuc y} p = absurd (pos≠negsuc p)
≤-refl' {negsuc x} {pos y} p = absurd (negsuc≠pos p)
≤-refl' {negsuc x} {negsuc y} p = neg≤neg (Nat.≤-refl' (negsuc-injective (sym p)))

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {pos x} {pos y} {pos z} x≤y y≤z = pos≤pos (Nat.≤-trans (unpos≤pos x≤y) (unpos≤pos y≤z))
≤-trans {negsuc x} {pos y} {pos z} x≤y y≤z = neg≤pos
≤-trans {negsuc x} {negsuc y} {pos z} x≤y y≤z = neg≤pos
≤-trans {negsuc x} {negsuc y} {negsuc z} x≤y y≤z = neg≤neg (Nat.≤-trans (unneg≤neg y≤z) (unneg≤neg x≤y))

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym {pos x} {pos y} x≤y y≤x = ap pos (Nat.≤-antisym (unpos≤pos x≤y) (unpos≤pos y≤x))
≤-antisym {negsuc x} {negsuc y} x≤y y≤x = ap negsuc (Nat.≤-antisym (unneg≤neg y≤x) (unneg≤neg x≤y))

apos≤apos : ∀ {x y} → x Nat.≤ y → assign pos x ≤ assign pos y
apos≤apos {x} {y} p = ≤-trans (≤-refl' (assign-pos x)) (≤-trans (pos≤pos p) (≤-refl' (sym (assign-pos y))))

unapos≤apos : ∀ {x y} → assign pos x ≤ assign pos y → x Nat.≤ y
unapos≤apos {x} {y} p = unpos≤pos (≤-trans (≤-refl' (sym (assign-pos x))) (≤-trans p (≤-refl' (assign-pos y))))
```

<!--
```agda
possuc≤possuc : ∀ {x y} → pos x ≤ pos y → possuc x ≤ possuc y
possuc≤possuc (lift x≤y) = lift x≤y

unpossuc≤possuc : ∀ {x y} → possuc x ≤ possuc y → pos x ≤ pos y
unpossuc≤possuc (lift x≤y) = lift x≤y

negpred≤negpred : ∀ {x y} → negsuc x ≤ negsuc y → negsuc (suc x) ≤ negsuc (suc y)
negpred≤negpred (lift x≤y) = lift x≤y

unnegpred≤negpred : ∀ {x y} → negsuc (suc x) ≤ negsuc (suc y) → negsuc x ≤ negsuc y
unnegpred≤negpred (lift x≤y) = lift x≤y

posz≤pos : ∀ {x} → posz ≤ pos x
posz≤pos = lift oh

neg≤negone : ∀ {x} → negsuc x ≤ negsuc zero
neg≤negone = lift oh
```
-->

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
  Dec-≤ {x} {y} with oh? (x ≤? y)
  ... | yes x≤y = yes (lift x≤y)
  ... | no ¬x≤y = no (¬x≤y ∘ _≤_.lower)
```

<!--
```agda
  H-Level-≤ : ∀ {n x y} → H-Level (x ≤ y) (suc n)
  H-Level-≤ = prop-instance ≤-is-prop
```
-->

## Universal properties of maximum and minimum

This case bash shows that `maxℤ` and `minℤ` satisfy their
universal properties.

<!--
```agda
abstract
```
-->

```agda
  maxℤ-≤l : (x y : Int) → x ≤ maxℤ x y
  maxℤ-≤l (pos x)    (pos y)    = pos≤pos (Nat.max-≤l x y)
  maxℤ-≤l (pos _)    (negsuc _) = ≤-refl
  maxℤ-≤l (negsuc _) (pos _)    = neg≤pos
  maxℤ-≤l (negsuc x) (negsuc y) = neg≤neg (Nat.min-≤l x y)

  maxℤ-≤r : (x y : Int) → y ≤ maxℤ x y
  maxℤ-≤r (pos x)    (pos y)    = pos≤pos (Nat.max-≤r x y)
  maxℤ-≤r (pos _)    (negsuc _) = neg≤pos
  maxℤ-≤r (negsuc _) (pos _)    = ≤-refl
  maxℤ-≤r (negsuc x) (negsuc y) = neg≤neg (Nat.min-≤r x y)

  maxℤ-univ : (x y z : Int) → x ≤ z → y ≤ z → maxℤ x y ≤ z
  maxℤ-univ (pos x) (pos y) (pos z) x≤z y≤z = pos≤pos (Nat.max-univ x y z (unpos≤pos x≤z) (unpos≤pos y≤z))
  maxℤ-univ (pos x) (negsuc y) z x≤z y≤z = x≤z
  maxℤ-univ (negsuc x) (pos y) z x≤z y≤z = y≤z
  maxℤ-univ (negsuc x) (negsuc y) (pos z) x≤z y≤z = neg≤pos
  maxℤ-univ (negsuc x) (negsuc y) (negsuc z) x≥z y≥z = neg≤neg (Nat.min-univ x y z (unneg≤neg x≥z) (unneg≤neg y≥z))

  minℤ-≤l : (x y : Int) → minℤ x y ≤ x
  minℤ-≤l (pos x)    (pos y)    = pos≤pos (Nat.min-≤l x y)
  minℤ-≤l (pos _)    (negsuc _) = neg≤pos
  minℤ-≤l (negsuc _) (pos _)    = ≤-refl
  minℤ-≤l (negsuc x) (negsuc y) = neg≤neg (Nat.max-≤l x y)

  minℤ-≤r : (x y : Int) → minℤ x y ≤ y
  minℤ-≤r (pos x)    (pos y)    = pos≤pos (Nat.min-≤r x y)
  minℤ-≤r (pos _)    (negsuc _) = ≤-refl
  minℤ-≤r (negsuc _) (pos _)    = neg≤pos
  minℤ-≤r (negsuc x) (negsuc y) = neg≤neg (Nat.max-≤r x y)

  minℤ-univ : (x y z : Int) → z ≤ x → z ≤ y → z ≤ minℤ x y
  minℤ-univ (pos x) (pos y) (pos z) z≤x z≤y = pos≤pos (Nat.min-univ x y z (unpos≤pos z≤x) (unpos≤pos z≤y))
  minℤ-univ (pos x) (pos y) (negsuc z) z≤x z≤y = neg≤pos
  minℤ-univ (pos x) (negsuc y) z z≤x z≤y = z≤y
  minℤ-univ (negsuc x) (pos y) z z≤x z≤y = z≤x
  minℤ-univ (negsuc x) (negsuc y) (negsuc z) z≥x z≥y = neg≤neg (Nat.max-univ x y z (unneg≤neg z≥x) (unneg≤neg z≥y))
```

## Compatibility with the structure

The last case bash in this module will establish that the ordering on
integers is compatible with the successor, predecessor, and negation.
Since addition is equivalent to iterated application of the successor
and predecessor, we get as a corollary that addition also respects
the order.

```agda
abstract
  suc-≤ : ∀ x y → x ≤ y → sucℤ x ≤ sucℤ y
  suc-≤ (pos x) (pos y) x≤y = possuc≤possuc x≤y
  suc-≤ (negsuc zero) (pos x) x≤y = posz≤pos
  suc-≤ (negsuc zero) (negsuc zero) x≤y = ≤-refl
  suc-≤ (negsuc (suc x)) (pos y) x≤y = neg≤pos
  suc-≤ (negsuc (suc x)) (negsuc zero) x≤y = neg≤pos
  suc-≤ (negsuc (suc x)) (negsuc (suc y)) x≤y = unnegpred≤negpred x≤y

  pred-≤ : ∀ x y → x ≤ y → predℤ x ≤ predℤ y
  pred-≤ posz posz x≤y = ≤-refl
  pred-≤ posz (possuc y) x≤y = neg≤pos
  pred-≤ (possuc x) (possuc y) x≤y = pos≤pos (Nat.≤-peel (unpos≤pos x≤y))
  pred-≤ (negsuc x) posz x≤y = neg≤negone
  pred-≤ (negsuc x) (possuc y) x≤y = neg≤pos
  pred-≤ (negsuc x) (negsuc y) x≤y = negpred≤negpred x≤y

  rotℤ≤l : ∀ k x y → x ≤ y → rotℤ k x ≤ rotℤ k y
  rotℤ≤l posz             x y p = p
  rotℤ≤l (possuc k)       x y p = suc-≤ _ _ (rotℤ≤l (pos k) x y p)
  rotℤ≤l (negsuc zero)    x y p = pred-≤ _ _ p
  rotℤ≤l (negsuc (suc k)) x y p = pred-≤ _ _ (rotℤ≤l (negsuc k) x y p)

abstract
  +ℤ-preserves-≤l : ∀ k x y → x ≤ y → (k +ℤ x) ≤ (k +ℤ y)
  +ℤ-preserves-≤l k x y p = transport
    (sym (ap₂ _≤_ (rot-is-add k x) (rot-is-add k y)))
    (rotℤ≤l k x y p)

  +ℤ-preserves-≤r : ∀ k x y → x ≤ y → (x +ℤ k) ≤ (y +ℤ k)
  +ℤ-preserves-≤r k x y p = transport
    (ap₂ _≤_ (+ℤ-commutative k x) (+ℤ-commutative k y))
    (+ℤ-preserves-≤l k x y p)

  negℤ-anti : ∀ x y → x ≤ y → negℤ y ≤ negℤ x
  negℤ-anti posz       posz       x≤y = x≤y
  negℤ-anti posz       (possuc y) _   = neg≤pos
  negℤ-anti (possuc x) (possuc y) x≤y = neg≤neg (Nat.≤-peel (unpos≤pos x≤y))
  negℤ-anti (negsuc _) posz       _   = posz≤pos
  negℤ-anti (negsuc _) (possuc y) _   = neg≤pos
  negℤ-anti (negsuc x) (negsuc y) x≤y = pos≤pos (Nat.s≤s (unneg≤neg x≤y))

  negℤ-anti-full : ∀ x y → negℤ y ≤ negℤ x → x ≤ y
  negℤ-anti-full x y -x≤-y =
    subst₂ _≤_ (negℤ-negℤ x) (negℤ-negℤ y)
    $ negℤ-anti (negℤ y) (negℤ x) -x≤-y

  *ℤ-cancel-≤r : ∀ {x y z} ⦃ _ : Positive x ⦄ → (y *ℤ x) ≤ (z *ℤ x) → y ≤ z
  *ℤ-cancel-≤r {possuc x} {y = pos y} {pos z} ⦃ pos _ ⦄ p = pos≤pos
    (Nat.*-reflects-≤r (suc x) (unapos≤apos p))
  *ℤ-cancel-≤r {possuc x} {y = pos y} {negsuc z} ⦃ pos _ ⦄ p = absurd (¬pos≤neg (≤-trans (≤-refl' (sym (assign-pos (y * suc x)))) p))
  *ℤ-cancel-≤r {possuc x} {y = negsuc y} {pos z} ⦃ pos _ ⦄ p = neg≤pos
  *ℤ-cancel-≤r {possuc x} {y = negsuc y} {negsuc z} ⦃ pos _ ⦄ p = neg≤neg
    (Nat.*-reflects-≤r (suc x) (Nat.+-reflects-≤l (z * suc x) (y * suc x) x (unneg≤neg p)))

  *ℤ-cancel-≤l : ∀ {x y z} ⦃ _ : Positive x ⦄ → (x *ℤ y) ≤ (x *ℤ z) → y ≤ z
  *ℤ-cancel-≤l {x} {y} {z} p = *ℤ-cancel-≤r {x} {y} {z} (≤-trans (≤-refl' (*ℤ-commutative y x)) (≤-trans p (≤-refl' (*ℤ-commutative x z))))

  *ℤ-preserves-≤r : ∀ {x y} z ⦃ _ : Positive z ⦄ → x ≤ y → (x *ℤ z) ≤ (y *ℤ z)
  *ℤ-preserves-≤r {pos x} {pos y} (possuc z) ⦃ pos z ⦄ p = apos≤apos {x * suc z} {y * suc z} (Nat.*-preserves-≤r x y (suc z) (unpos≤pos p))
  *ℤ-preserves-≤r {negsuc x} {pos y} (possuc z) ⦃ pos z ⦄ p = ≤-trans neg≤pos (≤-refl' (sym (assign-pos (y * suc z))))
  *ℤ-preserves-≤r {negsuc x} {negsuc y} (possuc z) ⦃ pos z ⦄ p = neg≤neg (Nat.+-preserves-≤l (y * suc z) (x * suc z) z (Nat.*-preserves-≤r y x (suc z) (unneg≤neg p)))

  *ℤ-nonnegative : ∀ {x y} → 0 ≤ x → 0 ≤ y → 0 ≤ (x *ℤ y)
  *ℤ-nonnegative {pos x} {pos y} 0≤x 0≤y = ≤-trans posz≤pos (≤-refl' (sym (assign-pos (x * y))))

  positive→nonnegative : ∀ {x} → Positive x → 0 ≤ x
  positive→nonnegative (pos x) = pos≤pos Nat.0≤x

  -ℕ-nonnegative : ∀ {x y} → y Nat.≤ x → 0 ≤ (x ℕ- y)
  -ℕ-nonnegative {x} {zero} y≤x = posz≤pos
  -ℕ-nonnegative {suc x} {suc y} y≤x = -ℕ-nonnegative (Nat.≤-peel y≤x)

  -ℤ-nonnegative : ∀ {x y} → 0 ≤ x → 0 ≤ y → y ≤ x → 0 ≤ (x -ℤ y)
  -ℤ-nonnegative {pos x} {posz} 0≤x 0≤y y≤x = posz≤pos
  -ℤ-nonnegative {pos x} {possuc y} 0≤x 0≤y y≤x = -ℕ-nonnegative (unpos≤pos y≤x)
```

# The strict order

```agda
_<?_ : Int → Int → Bool
pos x    <? pos y    = x Nat.<? y
pos x    <? negsuc y = false
negsuc x <? pos y    = true
negsuc x <? negsuc y = y Nat.<? x

record _<_ (x y : Int) : Type where
  constructor lift
  field
    lower : So (x <? y)
```

<!--
```agda
instance
  H-Level-< : ∀ {x y n} → H-Level (x < y) (suc n)
  H-Level-< = prop-instance λ _ _ → refl

abstract
  pos<pos : ∀ {x y} → x Nat.< y → pos x < pos y
  pos<pos (Nat.lift x<y) = lift x<y

  unpos<pos : ∀ {x y} → pos x < pos y → x Nat.< y
  unpos<pos (lift x<y) = Nat.lift x<y

  neg<pos : ∀ {x y} → negsuc x < pos y
  neg<pos = lift oh

  neg<neg : ∀ {x y} → y Nat.< x → negsuc x < negsuc y
  neg<neg (Nat.lift y<x) = lift y<x

  unneg<neg : ∀ {x y} → negsuc x < negsuc y → y Nat.< x
  unneg<neg (lift x<y) = Nat.lift x<y
```
-->

```agda
<-dec : ∀ x y → Dec (x < y)
<-dec x y with oh? (x <? y)
... | yes x<y = yes (lift x<y)
... | no ¬x<y = no (¬x<y ∘ _<_.lower)

instance
  Dec-< : ∀ {x y} → Dec (x < y)
  Dec-< {x} {y} = <-dec x y

abstract
  <-≤-asym : ∀ {x y} → x < y → ¬ (y ≤ x)
  <-≤-asym {pos x} {pos y} x<y y≤x = absurd (Nat.<-≤-asym (unpos<pos x<y) (unpos≤pos y≤x))
  <-≤-asym {negsuc x} {negsuc y} x<y y≤x = absurd (Nat.<-≤-asym (unneg<neg x<y) (unneg≤neg y≤x))

  <-not-equal : ∀ {x y} → x < y → x ≠ y
  <-not-equal x<y x=y = <-≤-asym x<y (≤-refl' (sym x=y))

  <-irrefl : ∀ {x y} → x ≡ y → ¬ (x < y)
  <-irrefl p q = <-not-equal q p

  <-weaken : ∀ {x y} → x < y → x ≤ y
  <-weaken {x} {y} x<y = ≤-is-weakly-total y x (<-≤-asym x<y)

  <-asym : ∀ {x y} → x < y → ¬ (y < x)
  <-asym x<y y<x = <-≤-asym x<y (<-weaken y<x)

  ≤-from-not-< : ∀ {x y} → ¬ x < y → y ≤ x
  ≤-from-not-< {pos x} {pos y} ¬x<y = pos≤pos (Nat.≤-from-not-< x y (¬x<y ∘ pos<pos))
  ≤-from-not-< {pos x} {negsuc y} ¬x<y = neg≤pos
  ≤-from-not-< {negsuc x} {pos y} ¬x<y = absurd (¬x<y neg<pos)
  ≤-from-not-< {negsuc x} {negsuc y} ¬x<y = neg≤neg (Nat.≤-from-not-< y x (¬x<y ∘ neg<neg))

  <-from-not-≤ : ∀ {x y} → ¬ (x ≤ y) → y < x
  <-from-not-≤ = contrapose λ ¬y<x ¬x≤y → ¬x≤y (≤-from-not-< ¬y<x)

  <-from-≤ : ∀ {x y} → x ≤ y → x ≠ y → x < y
  <-from-≤ x≤y x≠y = <-from-not-≤ λ y≤x → x≠y (≤-antisym x≤y y≤x)

<-linear : ∀ {x y} → ¬ x < y → ¬ y < x → x ≡ y
<-linear {x} {y} ¬x<y ¬y<x = ≤-antisym (≤-from-not-< ¬y<x) (≤-from-not-< ¬x<y)

<-split : ∀ x y → (x < y) ⊎ (x ≡ y) ⊎ (y < x)
<-split x y with <-dec x y
... | yes x<y = inl x<y
... | no ¬x<y with <-dec y x
... | yes y<x = inr (inr y<x)
... | no ¬y<x = inr (inl (<-linear ¬x<y ¬y<x))

≤-strengthen : ∀ {x y} → x ≤ y → (x ≡ y) ⊎ (x < y)
≤-strengthen {x} {y} x≤y with <-split x y
... | inl x<y = inr x<y
... | inr (inl x=y) = inl x=y
... | inr (inr y<x) = absurd (<-≤-asym y<x x≤y)

abstract
  <-≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z
  <-≤-trans x<y y≤z = <-from-not-≤ λ z≤x → <-≤-asym x<y (≤-trans y≤z z≤x)

  ≤-<-trans : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤-<-trans x≤y y<z = <-from-not-≤ λ z≤x → <-≤-asym y<z (≤-trans z≤x x≤y)

  <-trans : ∀ {x y z} → x < y → y < z → x < z
  <-trans x<y y<z = <-≤-trans x<y (<-weaken y<z)

  nat-diff-<-possuc : ∀ k x → (k ℕ- x) < possuc k
  nat-diff-<-possuc zero zero = pos<pos (Nat.s≤s Nat.0≤x)
  nat-diff-<-possuc zero (suc x) = neg<pos
  nat-diff-<-possuc (suc k) zero = pos<pos Nat.≤-refl
  nat-diff-<-possuc (suc k) (suc x) = <-trans (nat-diff-<-possuc k x) (pos<pos Nat.≤-refl)

  nat-diff-<-pos : ∀ k x → (k ℕ- suc x) < pos k
  nat-diff-<-pos zero zero = neg<pos
  nat-diff-<-pos zero (suc x) = neg<pos
  nat-diff-<-pos (suc k) zero = pos<pos auto
  nat-diff-<-pos (suc k) (suc x) = nat-diff-<-possuc k (suc x)

  negsuc-<-nat-diff : ∀ k x → negsuc k < (x ℕ- k)
  negsuc-<-nat-diff zero zero = neg<pos
  negsuc-<-nat-diff zero (suc x) = neg<pos
  negsuc-<-nat-diff (suc k) zero = neg<neg auto
  negsuc-<-nat-diff (suc k) (suc x) = <-trans (neg<neg auto) (negsuc-<-nat-diff k x)

  negsuc-≤-nat-diff : ∀ k x → negsuc k ≤ (x ℕ- suc k)
  negsuc-≤-nat-diff zero zero = neg≤neg Nat.0≤x
  negsuc-≤-nat-diff zero (suc x) = neg≤pos
  negsuc-≤-nat-diff (suc k) zero = neg≤neg auto
  negsuc-≤-nat-diff (suc k) (suc x) = ≤-trans (neg≤neg Nat.≤-ascend) (negsuc-≤-nat-diff k x)

  nat-diff-preserves-<r : ∀ k {x y} → y Nat.< x → (k ℕ- x) < (k ℕ- y)
  nat-diff-preserves-<r zero {suc zero} {zero} y<x = neg<pos
  nat-diff-preserves-<r zero {suc (suc x)} {zero} y<x = neg<pos
  nat-diff-preserves-<r zero {suc (suc x)} {suc y} y<x = neg<neg (Nat.≤-peel y<x)
  nat-diff-preserves-<r (suc k) {suc x} {zero} y<x = nat-diff-<-possuc k x
  nat-diff-preserves-<r (suc k) {suc x} {suc y} y<x = nat-diff-preserves-<r k {x} {y} (Nat.≤-peel y<x)

  nat-diff-preserves-<l : ∀ k {x y} → x Nat.< y → (x ℕ- k) < (y ℕ- k)
  nat-diff-preserves-<l zero {zero} {suc y} x<y = pos<pos (Nat.s≤s Nat.0≤x)
  nat-diff-preserves-<l zero {suc x} {suc y} x<y = pos<pos x<y
  nat-diff-preserves-<l (suc k) {zero} {suc y} x<y = negsuc-<-nat-diff k y
  nat-diff-preserves-<l (suc k) {suc x} {suc y} x<y = nat-diff-preserves-<l k {x} {y} (Nat.≤-peel x<y)

  +ℤ-preserves-<r : ∀ x y z → x < y → (x +ℤ z) < (y +ℤ z)
  +ℤ-preserves-<r (pos x) (pos y) (pos z) x<y = pos<pos (Nat.+-preserves-<r _ _ z (unpos<pos x<y))
  +ℤ-preserves-<r (negsuc x) (pos y) (pos z) neg<pos =
    let
      rem₁ : z Nat.≤ y + z
      rem₁ = Nat.≤-trans (Nat.+-≤l z y) (Nat.≤-refl' (Nat.+-commutative z y))
    in <-≤-trans (nat-diff-<-pos z x) (pos≤pos rem₁)
  +ℤ-preserves-<r (negsuc x) (negsuc y) (pos z) x<y = nat-diff-preserves-<r z (Nat.s≤s (unneg<neg x<y))
  +ℤ-preserves-<r (pos x) (pos y) (negsuc z) x<y = nat-diff-preserves-<l (suc z) (unpos<pos x<y)
  +ℤ-preserves-<r (negsuc x) (pos y) (negsuc z) neg<pos =
    let
      rem₁ : suc z Nat.≤ suc (x + z)
      rem₁ = Nat.≤-trans (Nat.+-≤l (suc z) x) (Nat.≤-refl' (ap suc (Nat.+-commutative z x)))
    in <-≤-trans (neg<neg rem₁) (negsuc-≤-nat-diff z y)
  +ℤ-preserves-<r (negsuc x) (negsuc y) (negsuc z) x<y = neg<neg (Nat.s≤s (Nat.+-preserves-<r _ _ z (unneg<neg x<y)))

  +ℤ-preserves-<l : ∀ x y z → x < y → (z +ℤ x) < (z +ℤ y)
  +ℤ-preserves-<l x y z p = subst₂ _<_ (+ℤ-commutative x z) (+ℤ-commutative y z) (+ℤ-preserves-<r x y z p)

  +ℤ-preserves-< : ∀ x y x' y' → x < y → x' < y' → (x +ℤ x') < (y +ℤ y')
  +ℤ-preserves-< x y x' y' p q = <-trans (+ℤ-preserves-<r x y x' p) (+ℤ-preserves-<l x' y' y q)

  *ℤ-cancel-<r : ∀ {x y z} ⦃ _ : Positive x ⦄ → (y *ℤ x) < (z *ℤ x) → y < z
  *ℤ-cancel-<r {x} {y} {z} yx<zx = <-from-≤
    (*ℤ-cancel-≤r {x} {y} {z} (<-weaken yx<zx))
    λ y=z → <-irrefl (ap (_*ℤ x) y=z) yx<zx

  *ℤ-cancel-<l : ∀ {x y z} ⦃ _ : Positive x ⦄ → (x *ℤ y) < (x *ℤ z) → y < z
  *ℤ-cancel-<l {x} {y} {z} xy<xz = *ℤ-cancel-<r {x} {y} {z} (subst₂ _<_ (*ℤ-commutative x y) (*ℤ-commutative x z) xy<xz)

  *ℤ-preserves-<r : ∀ {x y} z ⦃ _ : Positive z ⦄ → x < y → (x *ℤ z) < (y *ℤ z)
  *ℤ-preserves-<r {x} {y} z x<y = <-from-≤
    (*ℤ-preserves-≤r {x} {y} z (<-weaken x<y))
    λ xz=yz → <-irrefl (*ℤ-injectiver z x y (positive→nonzero auto) xz=yz) x<y

  negℤ-anti-< : ∀ {x y} → x < y → negℤ y < negℤ x
  negℤ-anti-< {posz} {possuc y} x<y = neg<pos
  negℤ-anti-< {possuc x} {possuc y} x<y = neg<neg (Nat.≤-peel (unpos<pos x<y))
  negℤ-anti-< {negsuc x} {posz} x<y = pos<pos (Nat.s≤s Nat.0≤x)
  negℤ-anti-< {negsuc x} {possuc y} x<y = neg<pos
  negℤ-anti-< {negsuc x} {negsuc y} x<y = pos<pos (Nat.s≤s (unneg<neg x<y))

  negℤ-anti-full-< : ∀ {x y} → negℤ x < negℤ y → y < x
  negℤ-anti-full-< {x} {y} p = subst₂ _<_ (negℤ-negℤ y) (negℤ-negℤ x) (negℤ-anti-< p)
```
