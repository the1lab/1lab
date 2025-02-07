<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Monoid

open import Data.Rational.Reflection
open import Data.Rational.Order
open import Data.Rational.Base
open import Data.Nat.Base hiding (Positive ; _<_ ; _≤_)

import Algebra.Ring.Reasoning as Kit

import Data.Int.Properties as ℤ
import Data.Int.Order as ℤ
import Data.Int.Base as ℤ
```
-->

```agda
module Data.Rational.Properties where
```

# Misc. properties of the rationals

<!--
```agda
private module ℚr = Kit (ℚ-ring .fst , record { CRing-on (ℚ-ring .snd) })
open ℚr renaming (*-negater to *ℚ-negater ; *-negatel to *ℚ-negatel) using () public

abstract
```
-->

## Properties of multiplication

```agda
  *ℚ-distrib-minusr : ∀ {x y z} → (y -ℚ z) *ℚ x ≡ y *ℚ x -ℚ z *ℚ x
  *ℚ-distrib-minusr {x@(inc _)} {y@(inc _)} {z@(inc _)} = *ℚ-distribr x y (-ℚ z) ∙ ap₂ _+ℚ_ (λ i → y *ℚ x) (ℚr.*-negatel {z} {x})

  *ℚ-distrib-minusl : ∀ {x y z} → x *ℚ (y -ℚ z) ≡ x *ℚ y -ℚ x *ℚ z
  *ℚ-distrib-minusl = *ℚ-commutative _ _ ∙ *ℚ-distrib-minusr ∙ ap₂ _-ℚ_ (*ℚ-commutative _ _) (*ℚ-commutative _ _)

  *ℚ-invl : ∀ {x} ⦃ p : Nonzero x ⦄ → invℚ x *ℚ x ≡ 1
  *ℚ-invl = *ℚ-commutative _ _ ∙ *ℚ-invr
```

## Nonzero rationals

```agda
  /ℚ-def : {x y : ℚ} ⦃ p : Nonzero y ⦄ → (x /ℚ y) ≡ x *ℚ invℚ y
  /ℚ-def {inc x} {inc y} = refl

  *ℚ-nonzero : ∀ {x y} → Nonzero x → Nonzero y → Nonzero (x *ℚ y)
  /ℚ-nonzero-num : ∀ {n d} ⦃ p : Nonzero d ⦄ → Nonzero (n /ℚ d) → Nonzero n
  negℚ-nonzero : ∀ {n} → Nonzero n → Nonzero (-ℚ n)
  invℚ-nonzero : ∀ {n} ⦃ d : Nonzero n ⦄ → Nonzero (invℚ n)

  unquoteDef *ℚ-nonzero /ℚ-nonzero-num negℚ-nonzero invℚ-nonzero = do
    by-elim-ℚ *ℚ-nonzero λ d a b α β →
      to-nonzero-frac (ℤ.*ℤ-nonzero (from-nonzero-frac α) (from-nonzero-frac β))

    by-elim-ℚ /ℚ-nonzero-num λ where
      d x ℤ.posz ⦃ p ⦄ nz → absurd (from-nonzero-frac p refl)
      d x (ℤ.possuc y) nz → to-nonzero-frac (ℤ.*ℤ-nonzero-cancel {x} {d} (from-nonzero-frac nz))
      (ℤ.possuc x) ⦃ ℤ.pos .x ⦄ y (ℤ.negsuc z) nz → to-nonzero-frac (ℤ.*ℤ-nonzero-cancel {y} {ℤ.negsuc x} (from-nonzero-frac nz))

    by-elim-ℚ negℚ-nonzero λ where
      d ℤ.posz (inc α) → absurd (α (quotℚ (to-same-rational refl)))
      d (ℤ.possuc x) (inc α) → to-nonzero-frac ℤ.negsuc≠pos
      d (ℤ.negsuc x) (inc α) → to-nonzero-frac (suc≠zero ∘ ℤ.pos-injective)

    by-elim-ℚ invℚ-nonzero λ where
      d ℤ.posz ⦃ inc α ⦄ → absurd (α (quotℚ (to-same-rational refl)))
      (ℤ.possuc d) ⦃ ℤ.pos .d ⦄ (ℤ.possuc x) ⦃ inc α ⦄ → to-nonzero-frac (suc≠zero ∘ ℤ.pos-injective)
      (ℤ.possuc d) ⦃ ℤ.pos .d ⦄ (ℤ.negsuc x) ⦃ inc α ⦄ → to-nonzero-frac ℤ.negsuc≠pos

  instance
    Nonzero-*ℚ : ∀ {x y : ℚ} ⦃ p : Nonzero x ⦄ ⦃ q : Nonzero y ⦄ → Nonzero (x *ℚ y)
    Nonzero-*ℚ ⦃ p ⦄ ⦃ q ⦄ = *ℚ-nonzero p q

    Nonzero-invℚ : ∀ {x} ⦃ p : Nonzero x ⦄ → Nonzero (invℚ x)
    Nonzero-invℚ ⦃ p ⦄ = invℚ-nonzero ⦃ p ⦄

    Nonzero-/ℚ : ∀ {x y} ⦃ p : Nonzero x ⦄ ⦃ q : Nonzero y ⦄ → Nonzero (x /ℚ y)
    Nonzero-/ℚ {x} {y} ⦃ p ⦄ ⦃ q ⦄ = subst Nonzero (sym /ℚ-def) (*ℚ-nonzero p invℚ-nonzero)

    {-# OVERLAPPABLE Nonzero-*ℚ Nonzero-invℚ Nonzero-/ℚ #-}
```

## Properties of division

```agda
  /ℚ-oner : ∀ x → x /ℚ 1 ≡ x
  /ℚ-oner (inc x) = *ℚ-idr (inc x)

  /ℚ-ap : ∀ {x y x' y'} {p : Nonzero y} {q : Nonzero y'} → x ≡ x' → y ≡ y' → (_/ℚ_ x y ⦃ p ⦄) ≡ (_/ℚ_ x' y' ⦃ q ⦄)
  /ℚ-ap {p = α} {β} p q i = _/ℚ_ (p i) (q i) ⦃ is-prop→pathp (λ i → hlevel {T = Nonzero (q i)} 1) α β i ⦄

  /ℚ-factorr : ∀ {x y} ⦃ p : Nonzero y ⦄ → (x *ℚ y) /ℚ y ≡ x
  /ℚ-factorr = /ℚ-def ∙ sym (*ℚ-associative _ _ _) ∙ ap₂ _*ℚ_ refl *ℚ-invr ∙ *ℚ-idr _

  /ℚ-self : ∀ {x} ⦃ p : Nonzero x ⦄ → x /ℚ x ≡ 1
  /ℚ-self {x} = /ℚ-def ∙ *ℚ-invr

  /ℚ-factorl : ∀ {x y} ⦃ p : Nonzero y ⦄ → (y *ℚ x) /ℚ y ≡ x
  /ℚ-factorl = /ℚ-ap (*ℚ-commutative _ _) refl ∙ /ℚ-factorr

  /ℚ-scaler : ∀ {x y z} ⦃ p : Nonzero y ⦄ → (x /ℚ y) *ℚ z ≡ (x *ℚ z) /ℚ y
  /ℚ-scaler = ap (_*ℚ _) /ℚ-def ∙ sym (*ℚ-associative _ _ _) ∙ ap (_ *ℚ_) (*ℚ-commutative _ _) ∙ *ℚ-associative _ _ _ ∙ sym /ℚ-def

  /ℚ-scalel : ∀ {x y z} ⦃ p : Nonzero z ⦄ → x *ℚ (y /ℚ z) ≡ (x *ℚ y) /ℚ z
  /ℚ-scalel {z = z} = *ℚ-commutative _ _ ∙ /ℚ-scaler ∙ ap (λ e → e /ℚ z) (*ℚ-commutative _ _)

  /ℚ-cross : ∀ {q q' d} ⦃ α : Nonzero d ⦄ → q *ℚ d ≡ q' → q ≡ (q' /ℚ d)
  /ℚ-cross {d = d} p = sym (ap (λ e → (e /ℚ d) ⦃ _ ⦄) (sym p) ∙ /ℚ-factorr)

  /ℚ-same
    : ∀ {q q' d d'} ⦃ α : Nonzero d ⦄ ⦃ β : Nonzero d' ⦄
    → q *ℚ d' ≡ q' *ℚ d → q /ℚ d ≡ q' /ℚ d'
  /ℚ-same p = /ℚ-cross (/ℚ-scaler ∙ sym (/ℚ-cross (sym p)))

  /ℚ-frac
    : ∀ {n d} ⦃ p : ℤ.Positive d ⦄
    → (n / 1) /ℚ (d / 1) ≡ (n / d)
  /ℚ-frac {n} {d = ℤ.possuc x} ⦃ p = ℤ.pos x ⦄ = quotℚ (to-same-rational (sym (ℤ.*ℤ-associative n 1 (ℤ.possuc x))))

  invℚ-*ℚ
    : ∀ {d d'} ⦃ p : Nonzero d ⦄ ⦃ p' : Nonzero d' ⦄
    → invℚ (d *ℚ d') ≡ invℚ d *ℚ invℚ d'
  invℚ-*ℚ {d} {d'} = monoid-inverse-unique *ℚ-monoid (d *ℚ d') _ _ *ℚ-invl
    (sym (*ℚ-associative _ _ _) ∙ ap (d *ℚ_)
      (ap (d' *ℚ_) (*ℚ-commutative _ _)
      ∙ *ℚ-associative d' _ _
      ∙ ap (_*ℚ invℚ d) *ℚ-invr ∙ *ℚ-idl (invℚ d))
    ∙ *ℚ-invr {d})

  invℚ-invℚ : ∀ {d} ⦃ p : Nonzero d ⦄ → invℚ (invℚ d) ≡ d
  invℚ-invℚ {d} = monoid-inverse-unique *ℚ-monoid (invℚ d) _ _ (*ℚ-commutative _ _ ∙ *ℚ-invr) (*ℚ-commutative _ _ ∙ *ℚ-invr)

  invℚ-/ℚ
    : ∀ {q d} ⦃ p : Nonzero d ⦄ ⦃ p' : Nonzero q ⦄
    → invℚ (q /ℚ d) ≡ (d /ℚ q)
  invℚ-/ℚ = ap₂ (λ e p → invℚ e ⦃ p ⦄) /ℚ-def prop! ∙ invℚ-*ℚ ∙ ap₂ _*ℚ_ refl invℚ-invℚ ∙ *ℚ-commutative _ _ ∙ sym /ℚ-def

  /ℚ-negatel
    : ∀ {q d} ⦃ p : Nonzero d ⦄ → -ℚ (q /ℚ d) ≡ (-ℚ q) /ℚ d
  /ℚ-negatel = ap -ℚ_ /ℚ-def ·· sym *ℚ-negatel ·· sym /ℚ-def

  /ℚ-def-+ℚ
    : ∀ {q q' d d'} ⦃ p : Nonzero d ⦄ ⦃ p' : Nonzero d' ⦄
    → (q /ℚ d) +ℚ (q' /ℚ d') ≡ ((q *ℚ d' +ℚ q' *ℚ d) /ℚ (d *ℚ d'))
  /ℚ-def-+ℚ {d = d} {d'} = /ℚ-cross
    (*ℚ-distribr _ _ _ ∙ ap₂ _+ℚ_
      (/ℚ-scaler ∙ ap (λ e → e /ℚ d) (ap (_ *ℚ_) (*ℚ-commutative d d') ∙ *ℚ-associative _ d' d) ∙ /ℚ-factorr)
      (/ℚ-scaler ∙ ap (λ e → e /ℚ d') (*ℚ-associative _ d d') ∙ /ℚ-factorr))

  /ℚ-def-subℚ
    : ∀ {q q' d d'} ⦃ p : Nonzero d ⦄ ⦃ p' : Nonzero d' ⦄
    → (q /ℚ d) -ℚ (q' /ℚ d') ≡ ((q *ℚ d' -ℚ q' *ℚ d) /ℚ (d *ℚ d'))
  /ℚ-def-subℚ {d = d} {d'} = /ℚ-cross
    (*ℚ-distrib-minusr ∙ ap₂ _-ℚ_
      (/ℚ-scaler ∙ ap (λ e → e /ℚ d) (ap (_ *ℚ_) (*ℚ-commutative d d') ∙ *ℚ-associative _ d' d) ∙ /ℚ-factorr)
      (/ℚ-scaler ∙ ap (λ e → e /ℚ d') (*ℚ-associative _ d d') ∙ /ℚ-factorr))

  /ℚ-def-*ℚ
    : ∀ {q q' d d'} ⦃ p : Nonzero d ⦄ ⦃ p' : Nonzero d' ⦄
    → (q /ℚ d) *ℚ (q' /ℚ d') ≡ (q *ℚ q') /ℚ (d *ℚ d')
  /ℚ-def-*ℚ {d = d} {d'} = /ℚ-cross
    (sym (*ℚ-associative _ _ _)
      ∙ ap (_ *ℚ_) (/ℚ-scaler ∙ ap (λ e → e /ℚ d') (*ℚ-associative _ d d') ∙ /ℚ-factorr)
      ∙ /ℚ-scaler ∙ ap (λ e → e /ℚ d) (*ℚ-associative _ _ d) ∙ /ℚ-factorr)
```

## Positivity

```agda
abstract
  *ℚ-positive : ∀ {x y} → Positive x → Positive y → Positive (x *ℚ y)
  +ℚ-positive : ∀ {x y} → Positive x → Positive y → Positive (x +ℚ y)
  +ℚ-nonneg-positive : ∀ {x y} → 0 ≤ x → Positive y → Positive (x +ℚ y)
  invℚ-positive : ∀ {d} (p : Positive d) → Positive (invℚ d ⦃ inc (positive→nonzero p) ⦄)

  unquoteDef *ℚ-positive +ℚ-positive invℚ-positive +ℚ-nonneg-positive = do
    by-elim-ℚ *ℚ-positive λ d a b (inc x) (inc y) → inc (ℤ.*ℤ-positive x y)
    by-elim-ℚ +ℚ-positive λ d a b (inc x) (inc y) → inc (ℤ.+ℤ-positive (ℤ.*ℤ-positive x auto) (ℤ.*ℤ-positive y auto))
    by-elim-ℚ invℚ-positive λ where
      d@(ℤ.possuc d') ⦃ ℤ.pos .d' ⦄ (ℤ.possuc x) px → inc (ℤ.pos d')

    by-elim-ℚ +ℚ-nonneg-positive λ where
      d (ℤ.posz) b (inc x) (inc y) → inc (subst ℤ.Positive (sym (ℤ.+ℤ-zerol (b ℤ.*ℤ d))) (ℤ.*ℤ-positive y auto))
      d (ℤ.possuc a) b (inc x) (inc y) → inc (ℤ.+ℤ-positive {ℤ.possuc a ℤ.*ℤ d} {b ℤ.*ℤ d} (ℤ.*ℤ-positive (ℤ.pos a) auto) (ℤ.*ℤ-positive y auto))

  /ℚ-positive : ∀ {x y} (p : Positive x) (q : Positive y) → Positive ((x /ℚ y) ⦃ inc (positive→nonzero q) ⦄)
  /ℚ-positive {y = y} p q = subst Positive
    (sym (/ℚ-def ⦃ _ ⦄)) (*ℚ-positive p (invℚ-positive q))

  from-positive : ∀ {x} → Positive x → 0 < x
  to-positive : ∀ {x} → 0 < x → Positive x

  unquoteDef from-positive to-positive = do
    by-elim-ℚ from-positive λ where
      d (ℤ.possuc x) (inc (ℤ.pos .x)) → inc (ℤ.pos<pos (s≤s 0≤x))

    by-elim-ℚ to-positive λ where
      d (ℤ.pos zero) (inc p) → inc (absurd (ℤ.<-irrefl refl p))
      d (ℤ.pos (suc x)) (inc p) → inc (ℤ.pos x)

  absℚ-nonneg : ∀ {x} → 0 ≤ absℚ x
  unquoteDef absℚ-nonneg = by-elim-ℚ absℚ-nonneg λ where
    d (ℤ.pos x) → inc (ℤ.apos≤apos {0} {x * 1} 0≤x)
    d (ℤ.negsuc x) → inc (ℤ.pos≤pos 0≤x)
```

```agda
abstract
  negℚ-anti-< : ∀ {x y} → x < y → -ℚ y < -ℚ x
  negℚ-anti-full-< : ∀ {x y} → -ℚ x < -ℚ y → y < x

  unquoteDef negℚ-anti-< negℚ-anti-full-< = do
    by-elim-ℚ negℚ-anti-< λ d x y α → common-denom-< (ℤ.negℤ-anti-< (<-common-denom α))
    by-elim-ℚ negℚ-anti-full-< λ d x y α → common-denom-< (ℤ.negℤ-anti-full-< (<-common-denom α))
```
