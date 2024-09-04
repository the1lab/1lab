<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring.Localisation hiding (_/_)
open import Algebra.Ring.Commutative
open import Algebra.Monoid

open import Data.Set.Coequaliser hiding (_/_)
open import Data.Int.Properties
open import Data.Nat.Properties
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Int.Base
open import Data.Sum.Base
```
-->

```agda
module Data.Rational.Base where
```

# Rational numbers {defines="rational-numbers"}

The ring of **rational numbers**, $\bQ$, is the
[[localisation|localisation of a ring]] of the ring of [[integers]]
$\bZ$, inverting all non-zero elements. We've already done most of the
work in that module, but we're missing an (easy) proof that the product
of nonzero integers is nonzero.

```agda
Nonzero : Int → Ω
Nonzero x .∣_∣ = x ≠ 0
Nonzero x .is-tr = hlevel 1

Nonzero-mult : ∀ {x y} → x ∈ Nonzero → y ∈ Nonzero → (x *ℤ y) ∈ Nonzero
Nonzero-mult {x} {y} x≠0 y≠0 α with *ℤ-is-zero x y α
... | inl x=0 = x≠0 x=0
... | inr y=0 = y≠0 y=0

private
  module L = Loc ℤ-comm Nonzero record { has-1 = decide! ; has-* = Nonzero-mult }
  module ℤ = CRing ℤ-comm
```

Strictly speaking, the construction is now done. However, we provide a
set of `opaque`{.Agda} wrappers for the operations on $\bZ\loc{(\ne 0)}$
so that the casual user of $\bQ$ does not have to care about the
details. The first thing we rename are the algebraic operations:

```agda
opaque
  ℚ : Type
  ℚ = ⌞ L.S⁻¹R ⌟

  toℚ : Fraction {R = Int} (_∈ Nonzero) → ℚ
  toℚ = inc

  _+ℚ_ : ℚ → ℚ → ℚ
  _+ℚ_ = L._+ₗ_

  _*ℚ_ : ℚ → ℚ → ℚ
  _*ℚ_ = L._*ₗ_

  -ℚ_ : ℚ → ℚ
  -ℚ_ = L.-ₗ_
```

Next, we have an elimination principle, which states that $\bQ$ is a
quotient of the type of integer fractions: to show a [[proposition]] at
every $x : \bQ$, it suffices to do so at the fractions.

```agda
  ℚ-elim-prop
    : ∀ {ℓ} {P : ℚ → Type ℓ} (pprop : ∀ x → is-prop (P x))
    → (f : ∀ x → P (toℚ x))
    → ∀ x → P x
  ℚ-elim-prop pprop f = Coeq-elim-prop pprop f
```

<!--
```agda
  ℚ-elim-prop-β
    : ∀ {ℓ} {P : ℚ → Type ℓ} (pprop : ∀ x → is-prop (P x))
    → ∀ (f : ∀ x → P (toℚ x)) x
    → ℚ-elim-prop {P = P} pprop f (toℚ x) ≡ f x
  ℚ-elim-prop-β _ _ _ = refl

  {-# REWRITE ℚ-elim-prop-β #-}

  +ℚ-β : ∀ {x y} → toℚ x +ℚ toℚ y ≡ toℚ (L.+f x y)
  +ℚ-β = refl

  *ℚ-β : ∀ {x y} → toℚ x *ℚ toℚ y ≡ toℚ (L.*f x y)
  *ℚ-β = refl

  -ℚ-β : ∀ {x} → -ℚ (toℚ x) ≡ toℚ (L.-f x)
  -ℚ-β = refl

  {-# REWRITE +ℚ-β *ℚ-β -ℚ-β #-}
```
-->

Next, we show that sameness of fractions implies identity in $\bQ$, and
the converse is true as well:

```agda
opaque
  unfolding ℚ

  quotℚ : ∀ {x y} → x L.≈ y → toℚ x ≡ toℚ y
  quotℚ = quot

  unquotℚ : ∀ {x y} → toℚ x ≡ toℚ y → x L.≈ y
  unquotℚ = L.Fr.effective
```

Finally, we want to show that the type of rational numbers is discrete.
To do this, we have to show that sameness of integer fractions is
decidable, i.e. that, given fractions $x/s$ and $y/t$, we can decide
whether there exists a $u \ne 0$ with $uxt = uys$. This is not automatic
since $u$ can range over all integers! However, recall that this is
equivalent to $u(xt - ys) = 0$. Since we know that $\bZ$ has no
zerodivisors, if this is true, then either $u = 0$ or $xt - ys = 0$; by
assumption, it can not be $u$. But if $xt - ys = 0$, then $xt = ys$!
Conversely, if $xt = ys$, then we can take $u = 1$. Therefore, checking
sameness of fractions boils down to checking whether they
"cross-multiply" to the same thing.

```agda
Dec-same-rational : (x y : Fraction (_≠ 0)) → Dec (x L.≈ y)
Dec-same-rational f@(x / s [ _ ]) f'@(y / t [ _ ]) with x *ℤ t ≡? y *ℤ s
... | yes p = yes (L.inc 1 decide! (sym (*ℤ-associative 1 x t) ·· ap (1 *ℤ_) p ·· *ℤ-associative 1 y s))
... | no xt≠ys = no λ p → case L.≈→≈' p of λ u u≠0 p → case *ℤ-is-zero u _ p of λ where
  (inl u=0) → u≠0 u=0
  (inr xt-ys=0) → xt≠ys (ℤ.zero-diff xt-ys=0)
```

<!--
```agda
-- Since we want _≡?_ and friends to compute for toℚ, we'll define them
-- by a detour through boolean equality. We can define an equality map
--
--   sameℚ : ℚ → ℚ → Bool
--
-- using the pre-existing proof of Discrete-quotient. This map is much
-- easier to rewrite than the actual decision! In particular,
--
--  sameℚ (toℚ x) (toℚ y) = Dec→Bool (Dec-same-rational x y)
--
-- is a pretty normal equation, and Agda is happy with it. We can then
-- use sameℚ to define the Discrete-ℚ instance in a way that computes.

opaque
  unfolding ℚ

  private
    _≡ℚ?_ : (x y : ℚ) → Dec (x ≡ y)
    x ≡ℚ? y = Discrete-quotient L.Fraction-congruence Dec-same-rational {x} {y}

  sameℚ : ℚ → ℚ → Bool
  sameℚ x y = Dec→Bool (x ≡ℚ? y)

  sameℚ-β : ∀ {x y} → sameℚ (toℚ x) (toℚ y) ≡ Dec→Bool (Dec-same-rational x y)
  sameℚ-β {x} {y} with Dec-same-rational x y
  ... | yes p = refl
  ... | no ¬p = refl

  {-# REWRITE sameℚ-β #-}

  from-sameℚ : ∀ {x y} → ⌞ sameℚ x y ⌟ → x ≡ y
  from-sameℚ {x} {y} p with x ≡ℚ? y | p
  ... | yes q | p = q
  ... | no ¬q | ()

  to-sameℚ : ∀ {x y} → x ≡ y → ⌞ sameℚ x y ⌟
  to-sameℚ {x} {y} p with x ≡ℚ? y
  ... | yes p = oh
  ... | no ¬p = absurd (¬p p)
```
-->

<details>
<summary>
There are a number of other properties of $\bZ{\loc{\ne 0}}$ that we can
export as properties of $\bQ$; however, these are all trivial as above,
so we do not remark on them any further.
</summary>

```agda
_-ℚ_ : ℚ → ℚ → ℚ
x -ℚ y = x +ℚ (-ℚ y)

infixl 8 _+ℚ_ _-ℚ_
infixl 9 _*ℚ_
infix 10 -ℚ_

_/_ : (x y : Int) ⦃ d : Dec (y ≠ 0) ⦄ {_ : is-yes d} → ℚ
_/_ x y ⦃ yes p ⦄ = toℚ (x / y [ p ])

{-# DISPLAY toℚ (_/_[_] x y p) = x / y #-}

_/1 : Int → ℚ
x /1 = x / 1

instance
  Discrete-ℚ : Discrete ℚ
  Discrete-ℚ {x} {y} with holds? (So (sameℚ x y))
  ... | yes p = yes (from-sameℚ p)
  ... | no ¬p = no λ p → ¬p (to-sameℚ p)

  H-Level-ℚ : ∀ {n} → H-Level ℚ (2 + n)
  H-Level-ℚ = basic-instance 2 (Discrete→is-set auto)

  Number-ℚ : Number ℚ
  Number-ℚ .Number.Constraint _ = ⊤
  Number-ℚ .Number.fromNat x = pos x /1

  Negative-ℚ : Negative ℚ
  Negative-ℚ .Negative.Constraint _ = ⊤
  Negative-ℚ .Negative.fromNeg 0 = 0
  Negative-ℚ .Negative.fromNeg (suc x) = negsuc x /1

abstract opaque
  unfolding ℚ

  +ℚ-idl : ∀ x → 0 +ℚ x ≡ x
  +ℚ-idl = L.+ₗ-idl

  +ℚ-idr : ∀ x → x +ℚ 0 ≡ x
  +ℚ-idr x = CRing.+-idr L.S⁻¹R

  +ℚ-associative : ∀ x y z → x +ℚ (y +ℚ z) ≡ (x +ℚ y) +ℚ z
  +ℚ-associative = L.+ₗ-assoc

  +ℚ-commutative : ∀ x y → x +ℚ y ≡ y +ℚ x
  +ℚ-commutative = L.+ₗ-comm

  *ℚ-idl : ∀ x → 1 *ℚ x ≡ x
  *ℚ-idl = L.*ₗ-idl

  *ℚ-idr : ∀ x → x *ℚ 1 ≡ x
  *ℚ-idr x = CRing.*-idr L.S⁻¹R

  *ℚ-associative : ∀ x y z → x *ℚ (y *ℚ z) ≡ (x *ℚ y) *ℚ z
  *ℚ-associative = L.*ₗ-assoc

  *ℚ-commutative : ∀ x y → x *ℚ y ≡ y *ℚ x
  *ℚ-commutative = L.*ₗ-comm

  *ℚ-zerol : ∀ x → 0 *ℚ x ≡ 0
  *ℚ-zerol x = CRing.*-zerol L.S⁻¹R {f = x}

  *ℚ-zeror : ∀ x → x *ℚ 0 ≡ 0
  *ℚ-zeror x = CRing.*-zeror L.S⁻¹R {f = x}

  *ℚ-distribl : ∀ x y z → x *ℚ (y +ℚ z) ≡ x *ℚ y +ℚ x *ℚ z
  *ℚ-distribl = L.*ₗ-distribl

+ℚ-monoid : is-monoid 0 _+ℚ_
+ℚ-monoid = record { has-is-semigroup = record { has-is-magma = record { has-is-set = hlevel 2 } ; associative = λ {x} {y} {z} → +ℚ-associative x y z } ; idl = +ℚ-idl _ ; idr = +ℚ-idr _ }

*ℚ-monoid : is-monoid 1 _*ℚ_
*ℚ-monoid = record { has-is-semigroup = record { has-is-magma = record { has-is-set = hlevel 2 } ; associative = λ {x} {y} {z} → *ℚ-associative x y z } ; idl = *ℚ-idl _ ; idr = *ℚ-idr _ }
```

</details>

## As a field

An important property of the ring $\bQ$ is that any nonzero rational
number is invertible. Since inverses are unique when they exist --- the
type of inverses is a proposition --- it suffices to show this at the
more concrete level of integer fractions.

```agda
inverseℚ : (x : ℚ) → x ≠ 0 → Σ[ y ∈ ℚ ] (x *ℚ y ≡ 1)
inverseℚ = ℚ-elim-prop is-p go where
  abstract
    is-p : (x : ℚ) → is-prop (x ≠ 0 → Σ[ y ∈ ℚ ] (x *ℚ y ≡ 1))
    is-p x = Π-is-hlevel 1 λ _ (y , p) (z , q) → Σ-prop-path! (monoid-inverse-unique *ℚ-monoid x y z (*ℚ-commutative y x ∙ p) q)

    lemma : ∀ x y → 1 *ℤ (x *ℤ y) *ℤ 1 ≡ 1 *ℤ (y *ℤ x)
    lemma x y = ap (_*ℤ 1) (*ℤ-onel (x *ℤ y))
      ∙ *ℤ-oner (x *ℤ y) ∙ *ℤ-commutative x y ∙ sym (*ℤ-onel (y *ℤ x))
```

This leaves us with three cases: either the fraction $x/y$ had a
denominator of zero, contradicting our assumption, or its numerator is
also nonzero (either positive or negative), so that we can form the
fraction $y/x$. It's then routine to show that $(x/y)(y/x) = 1$ holds in
$\bQ$.

```agda
  go : (x : Fraction _) → toℚ x ≠ 0 → Σ[ y ∈ ℚ ] (toℚ x *ℚ y ≡ 1)
  go (posz / y [ _ ]) nz = absurd (nz (quotℚ (L.inc 1 decide! refl)))
  go (x@(possuc x') / y [ _ ]) nz = y / x , quotℚ (L.inc 1 decide! (lemma x y))
  go (x@(negsuc x') / y [ _ ]) nz = y / x , quotℚ (L.inc 1 decide! (lemma x y))
```
