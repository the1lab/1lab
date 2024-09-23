<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Data.Int.Properties
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
data _≤_ : Int → Int → Type where
  neg≤neg : ∀ {x y} → y Nat.≤ x → negsuc x ≤ negsuc y
  pos≤pos : ∀ {x y} → x Nat.≤ y → pos x    ≤ pos y
  neg≤pos : ∀ {x y}             → negsuc x ≤ pos y
```

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
≤-is-prop (neg≤neg p) (neg≤neg q) = ap neg≤neg (Nat.≤-is-prop p q)
≤-is-prop (pos≤pos p) (pos≤pos q) = ap pos≤pos (Nat.≤-is-prop p q)
≤-is-prop neg≤pos neg≤pos = refl

≤-refl : ∀ {x} → x ≤ x
≤-refl {x = pos x}    = pos≤pos Nat.≤-refl
≤-refl {x = negsuc x} = neg≤neg Nat.≤-refl

≤-refl' : ∀ {x y} → x ≡ y → x ≤ y
≤-refl' {pos x} {pos y} p = pos≤pos (Nat.≤-refl' (pos-injective p))
≤-refl' {pos x} {negsuc y} p = absurd (pos≠negsuc p)
≤-refl' {negsuc x} {pos y} p = absurd (negsuc≠pos p)
≤-refl' {negsuc x} {negsuc y} p = neg≤neg (Nat.≤-refl' (negsuc-injective (sym p)))

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans (neg≤neg p) (neg≤neg q) = neg≤neg (Nat.≤-trans q p)
≤-trans (neg≤neg p) neg≤pos     = neg≤pos
≤-trans (pos≤pos p) (pos≤pos q) = pos≤pos (Nat.≤-trans p q)
≤-trans neg≤pos (pos≤pos x)     = neg≤pos

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym (neg≤neg p) (neg≤neg q) = ap negsuc (Nat.≤-antisym q p)
≤-antisym (pos≤pos p) (pos≤pos q) = ap pos (Nat.≤-antisym p q)

unpos≤pos : ∀ {x y} → pos x ≤ pos y → x Nat.≤ y
unpos≤pos (pos≤pos p) = p

unneg≤neg : ∀ {x y} → negsuc x ≤ negsuc y → y Nat.≤ x
unneg≤neg (neg≤neg p) = p

apos≤apos : ∀ {x y} → x Nat.≤ y → assign pos x ≤ assign pos y
apos≤apos {x} {y} p = ≤-trans (≤-refl' (assign-pos x)) (≤-trans (pos≤pos p) (≤-refl' (sym (assign-pos y))))

unapos≤apos : ∀ {x y} → assign pos x ≤ assign pos y → x Nat.≤ y
unapos≤apos {x} {y} p = unpos≤pos (≤-trans (≤-refl' (sym (assign-pos x))) (≤-trans p (≤-refl' (assign-pos y))))
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
  maxℤ-univ _ _ _ (pos≤pos x≤z) (pos≤pos y≤z) = pos≤pos (Nat.max-univ _ _ _ x≤z y≤z)
  maxℤ-univ _ _ _ (pos≤pos x≤z) neg≤pos       = pos≤pos x≤z
  maxℤ-univ _ _ _ neg≤pos       (pos≤pos y≤z) = pos≤pos y≤z
  maxℤ-univ _ _ _ neg≤pos       neg≤pos       = neg≤pos
  maxℤ-univ _ _ _ (neg≤neg x≥z) (neg≤neg y≥z) = neg≤neg (Nat.min-univ _ _ _ x≥z y≥z)

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
  minℤ-univ _ _ _ (pos≤pos x≥z) (pos≤pos y≥z) = pos≤pos (Nat.min-univ _ _ _ x≥z y≥z)
  minℤ-univ _ _ _ neg≤pos       neg≤pos       = neg≤pos
  minℤ-univ _ _ _ neg≤pos       (neg≤neg y≤z) = neg≤neg y≤z
  minℤ-univ _ _ _ (neg≤neg x≤z) neg≤pos       = neg≤neg x≤z
  minℤ-univ _ _ _ (neg≤neg x≤z) (neg≤neg y≤z) = neg≤neg (Nat.max-univ _ _ _ x≤z y≤z)
```

## Compatibility with the structure

The last case bash in this module will establish that the ordering on
integers is compatible with the successor, predecessor, and negation.
Since addition is equivalent to iterated application of the successor
and predecessor, we get as a corollary that addition also respects
the order.

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
  +ℤ-preserves-≤l : ∀ k x y → x ≤ y → (k +ℤ x) ≤ (k +ℤ y)
  +ℤ-preserves-≤l k x y p = transport
    (sym (ap₂ _≤_ (rot-is-add k x) (rot-is-add k y)))
    (rotℤ≤l k x y p)

  +ℤ-preserves-≤r : ∀ k x y → x ≤ y → (x +ℤ k) ≤ (y +ℤ k)
  +ℤ-preserves-≤r k x y p = transport
    (ap₂ _≤_ (+ℤ-commutative k x) (+ℤ-commutative k y))
    (+ℤ-preserves-≤l k x y p)

  negℤ-anti : ∀ x y → x ≤ y → negℤ y ≤ negℤ x
  negℤ-anti posz       posz       x≤y                     = x≤y
  negℤ-anti posz       (possuc y) _                       = neg≤pos
  negℤ-anti (possuc x) (possuc y) (pos≤pos (Nat.s≤s x≤y)) = neg≤neg x≤y
  negℤ-anti (negsuc _) posz       _                       = pos≤pos Nat.0≤x
  negℤ-anti (negsuc _) (possuc y) _                       = neg≤pos
  negℤ-anti (negsuc x) (negsuc y) (neg≤neg x≤y)           = pos≤pos (Nat.s≤s x≤y)

  negℤ-anti-full : ∀ x y → negℤ y ≤ negℤ x → x ≤ y
  negℤ-anti-full posz       (pos y)    _                       = pos≤pos Nat.0≤x
  negℤ-anti-full posz       (negsuc y) (pos≤pos ())
  negℤ-anti-full (possuc x) (possuc y) (neg≤neg x≤y)           = pos≤pos (Nat.s≤s x≤y)
  negℤ-anti-full (negsuc x) (pos y)    _                       = neg≤pos
  negℤ-anti-full (negsuc x) (negsuc y) (pos≤pos (Nat.s≤s y≤x)) = neg≤neg y≤x

  *ℤ-cancel-≤r : ∀ {x y z} ⦃ _ : Positive x ⦄ → (y *ℤ x) ≤ (z *ℤ x) → y ≤ z
  *ℤ-cancel-≤r {possuc x} {y = pos y} {pos z} ⦃ pos _ ⦄ p = pos≤pos
    (Nat.*-cancel-≤r (suc x) (unapos≤apos p))
  *ℤ-cancel-≤r {possuc x} {y = pos y} {negsuc z} ⦃ pos _ ⦄ p = absurd (¬pos≤neg (≤-trans (≤-refl' (sym (assign-pos (y * suc x)))) p))
  *ℤ-cancel-≤r {possuc x} {y = negsuc y} {pos z} ⦃ pos _ ⦄ p = neg≤pos
  *ℤ-cancel-≤r {possuc x} {y = negsuc y} {negsuc z} ⦃ pos _ ⦄ p = neg≤neg
    (Nat.*-cancel-≤r (suc x) (Nat.+-reflects-≤l (z * suc x) (y * suc x) x (unneg≤neg p)))

  *ℤ-preserves-≤r : ∀ {x y} z ⦃ _ : Positive z ⦄ → x ≤ y → (x *ℤ z) ≤ (y *ℤ z)
  *ℤ-preserves-≤r {pos x} {pos y} (possuc z) ⦃ pos z ⦄ p = apos≤apos {x * suc z} {y * suc z} (Nat.*-preserves-≤r x y (suc z) (unpos≤pos p))
  *ℤ-preserves-≤r {negsuc x} {pos y} (possuc z) ⦃ pos z ⦄ p = ≤-trans neg≤pos (≤-refl' (sym (assign-pos (y * suc z))))
  *ℤ-preserves-≤r {negsuc x} {negsuc y} (possuc z) ⦃ pos z ⦄ p = neg≤neg (Nat.+-preserves-≤l (y * suc z) (x * suc z) z (Nat.*-preserves-≤r y x (suc z) (unneg≤neg p)))

  *ℤ-nonnegative : ∀ {x y} → 0 ≤ x → 0 ≤ y → 0 ≤ (x *ℤ y)
  *ℤ-nonnegative {pos x} {pos y} (pos≤pos p) (pos≤pos q) = ≤-trans (pos≤pos Nat.0≤x) (≤-refl' (sym (assign-pos (x * y))))

  positive→nonnegative : ∀ {x} → Positive x → 0 ≤ x
  positive→nonnegative (pos x) = pos≤pos Nat.0≤x

  -ℕ-nonnegative : ∀ {x y} → y Nat.≤ x → 0 ≤ (x ℕ- y)
  -ℕ-nonnegative {x} {y} Nat.0≤x = pos≤pos Nat.0≤x
  -ℕ-nonnegative {suc x} {suc y} (Nat.s≤s p) = -ℕ-nonnegative p

  -ℤ-nonnegative : ∀ {x y} → 0 ≤ x → 0 ≤ y → y ≤ x → 0 ≤ (x -ℤ y)
  -ℤ-nonnegative {posz} {posz} (pos≤pos p) (pos≤pos q) (pos≤pos r) = pos≤pos Nat.0≤x
  -ℤ-nonnegative {possuc x} {posz} (pos≤pos p) (pos≤pos q) (pos≤pos r) = pos≤pos Nat.0≤x
  -ℤ-nonnegative {possuc x} {possuc y} (pos≤pos p) (pos≤pos q) (pos≤pos r) = -ℕ-nonnegative (Nat.≤-peel r)
```

# The strict order

```agda
data _<_ : Int → Int → Type where
  pos<pos : ∀ {x y} → x Nat.< y → pos x < pos y
  neg<pos : ∀ {x y} → negsuc x < pos y
  neg<neg : ∀ {x y} → y Nat.< x → negsuc x < negsuc y

instance
  H-Level-< : ∀ {x y n} → H-Level (x < y) (suc n)
  H-Level-< = prop-instance λ where
    (pos<pos x) (pos<pos y) → ap pos<pos (Nat.≤-is-prop x y)
    neg<pos neg<pos → refl
    (neg<neg x) (neg<neg y) → ap neg<neg (Nat.≤-is-prop x y)

<-not-equal : ∀ {x y} → x < y → x ≠ y
<-not-equal (pos<pos p) q = Nat.<-not-equal p (pos-injective q)
<-not-equal neg<pos q = negsuc≠pos q
<-not-equal (neg<neg p) q = Nat.<-not-equal p (negsuc-injective (sym q))

<-irrefl : ∀ {x y} → x ≡ y → ¬ (x < y)
<-irrefl p q = <-not-equal q p

<-weaken : ∀ {x y} → x < y → x ≤ y
<-weaken (pos<pos x) = pos≤pos (Nat.<-weaken x)
<-weaken neg<pos = neg≤pos
<-weaken (neg<neg x) = neg≤neg (Nat.<-weaken x)

<-asym : ∀ {x y} → x < y → ¬ (y < x)
<-asym (pos<pos x) (pos<pos y) = Nat.<-asym x y
<-asym (neg<neg x) (neg<neg y) = Nat.<-asym x y

≤-strengthen : ∀ {x y} → x ≤ y → (x ≡ y) ⊎ (x < y)
≤-strengthen (neg≤neg x) with Nat.≤-strengthen x
... | inl x=y = inl (ap negsuc (sym x=y))
... | inr x<y = inr (neg<neg x<y)
≤-strengthen (pos≤pos x) with Nat.≤-strengthen x
... | inl x=y = inl (ap pos x=y)
... | inr x<y = inr (pos<pos x<y)
≤-strengthen neg≤pos = inr neg<pos

<-from-≤ : ∀ {x y} → x ≤ y → x ≠ y → x < y
<-from-≤ x≤y x≠y with ≤-strengthen x≤y
... | inl x=y = absurd (x≠y x=y)
... | inr p = p

<-dec : ∀ x y → Dec (x < y)
<-dec (pos x) (pos y) with Nat.≤-dec (suc x) y
... | yes x<y = yes (pos<pos x<y)
... | no ¬x<y = no λ { (pos<pos x<y) → ¬x<y x<y }
<-dec (pos x) (negsuc y) = no λ ()
<-dec (negsuc x) (pos y) = yes neg<pos
<-dec (negsuc x) (negsuc y) with Nat.≤-dec (suc y) x
... | yes y<x = yes (neg<neg y<x)
... | no ¬y<x = no λ { (neg<neg y<x) → ¬y<x y<x }

instance
  Dec-< : ∀ {x y} → Dec (x < y)
  Dec-< {x} {y} = <-dec x y

≤-from-not-< : ∀ {x y} → ¬ x < y → y ≤ x
≤-from-not-< {pos x} {pos y} ¬x<y = pos≤pos (Nat.≤-from-not-< x y (λ x<y → ¬x<y (pos<pos x<y)))
≤-from-not-< {pos x} {negsuc y} ¬x<y = neg≤pos
≤-from-not-< {negsuc x} {pos y} ¬x<y = absurd (¬x<y neg<pos)
≤-from-not-< {negsuc x} {negsuc y} ¬x<y = neg≤neg (Nat.≤-from-not-< y x (λ y<x → ¬x<y (neg<neg y<x)))

<-linear : ∀ {x y} → ¬ x < y → ¬ y < x → x ≡ y
<-linear {x} {y} ¬x<y ¬y<x = ≤-antisym (≤-from-not-< ¬y<x) (≤-from-not-< ¬x<y)

<-split : ∀ x y → (x < y) ⊎ (x ≡ y) ⊎ (y < x)
<-split x y with <-dec x y
... | yes x<y = inl x<y
... | no ¬x<y with <-dec y x
... | yes y<x = inr (inr y<x)
... | no ¬y<x = inr (inl (<-linear ¬x<y ¬y<x))

<-trans : ∀ {x y z} → x < y → y < z → x < z
<-trans (pos<pos p) (pos<pos q) = pos<pos (Nat.<-trans _ _ _ p q)
<-trans neg<pos (pos<pos q) = neg<pos
<-trans (neg<neg p) neg<pos = neg<pos
<-trans (neg<neg p) (neg<neg q) = neg<neg (Nat.<-trans _ _ _ q p)

<-≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z
<-≤-trans p q with ≤-strengthen q
... | inl y=z = subst₂ _<_ refl y=z p
... | inr y<z = <-trans p y<z

≤-<-trans : ∀ {x y z} → x ≤ y → y < z → x < z
≤-<-trans p q with ≤-strengthen p
... | inl x=y = subst₂ _<_ (sym x=y) refl q
... | inr x<y = <-trans x<y q

abstract
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
  nat-diff-preserves-<r zero {suc zero} {zero} (Nat.s≤s Nat.0≤x) = neg<pos
  nat-diff-preserves-<r zero {suc (suc x)} {zero} (Nat.s≤s p) = neg<pos
  nat-diff-preserves-<r zero {suc (suc x)} {suc y} (Nat.s≤s p) = neg<neg p
  nat-diff-preserves-<r (suc k) {suc x} {zero} (Nat.s≤s p) = nat-diff-<-possuc k x
  nat-diff-preserves-<r (suc k) {suc x} {suc y} (Nat.s≤s p) = nat-diff-preserves-<r k {x} {y} p

  nat-diff-preserves-<l : ∀ k {x y} → x Nat.< y → (x ℕ- k) < (y ℕ- k)
  nat-diff-preserves-<l zero {zero} {suc y} (Nat.s≤s p) = pos<pos (Nat.s≤s Nat.0≤x)
  nat-diff-preserves-<l zero {suc x} {suc y} (Nat.s≤s p) = pos<pos (Nat.s≤s p)
  nat-diff-preserves-<l (suc k) {zero} {suc y} (Nat.s≤s Nat.0≤x) = negsuc-<-nat-diff k y
  nat-diff-preserves-<l (suc k) {suc x} {suc y} (Nat.s≤s p) = nat-diff-preserves-<l k {x} {y} p

  +ℤ-preserves-<r : ∀ x y z → x < y → (x +ℤ z) < (y +ℤ z)
  +ℤ-preserves-<r x y (pos z) (pos<pos p) = pos<pos (Nat.+-preserves-<r _ _ z p)
  +ℤ-preserves-<r (negsuc x) (pos y) (pos z) neg<pos =
    let
      rem₁ : z Nat.≤ y + z
      rem₁ = Nat.≤-trans (Nat.+-≤l z y) (Nat.≤-refl' (Nat.+-commutative z y))
    in <-≤-trans (nat-diff-<-pos z x) (pos≤pos rem₁)
  +ℤ-preserves-<r x y (pos z) (neg<neg p) = nat-diff-preserves-<r z (Nat.s≤s p)
  +ℤ-preserves-<r x y (negsuc z) (pos<pos p) = nat-diff-preserves-<l (suc z) p
  +ℤ-preserves-<r (negsuc x) (pos y) (negsuc z) neg<pos =
    let
      rem₁ : suc z Nat.≤ suc (x + z)
      rem₁ = Nat.≤-trans (Nat.+-≤l (suc z) x) (Nat.≤-refl' (ap suc (Nat.+-commutative z x)))
    in <-≤-trans (neg<neg rem₁) (negsuc-≤-nat-diff z y)
  +ℤ-preserves-<r x y (negsuc z) (neg<neg p) = neg<neg (Nat.s≤s (Nat.+-preserves-<r _ _ z p))

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
  negℤ-anti-< {posz} {pos y} (pos<pos (Nat.s≤s p)) = neg<pos
  negℤ-anti-< {possuc x} {pos y} (pos<pos (Nat.s≤s p)) = neg<neg p
  negℤ-anti-< {negsuc x} {posz} neg<pos = pos<pos (Nat.s≤s Nat.0≤x)
  negℤ-anti-< {negsuc x} {possuc y} neg<pos = neg<pos
  negℤ-anti-< {negsuc x} {negsuc y} (neg<neg p) = pos<pos (Nat.s≤s p)

  negℤ-anti-full-< : ∀ {x y} → negℤ x < negℤ y → y < x
  negℤ-anti-full-< {x} {y} p = subst₂ _<_ (negℤ-negℤ y) (negℤ-negℤ x) (negℤ-anti-< p)
```
