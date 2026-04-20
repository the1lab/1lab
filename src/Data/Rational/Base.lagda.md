<!--
```agda
{-# OPTIONS --no-qualified-instances #-}
open import 1Lab.Extensionality
open import 1Lab.Prelude

open import Algebra.Ring.Localisation hiding (_/_ ; Fraction)
open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver
open import Algebra.Monoid
open import Algebra.Ring hiding (fst; snd)

open import Data.Set.Coequaliser.Split
open import Data.Nat.Divisible.GCD
open import Data.Set.Coequaliser hiding (_/_)
open import Data.Fin.Properties
open import Data.Int.Properties
open import Data.Nat.Properties
open import Data.Nat.Divisible
open import Data.Fin.Product
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Int.Base
open import Data.Nat.Base hiding (Positive)
open import Data.Sum.Base
```
-->

```agda
module Data.Rational.Base where
```

# Rational numbers {defines="rational-numbers"}

The ring of **rational numbers**, $\bQ$, is the
[[localisation|localisation of a ring]] of the ring of [[integers]]
$\bZ$, inverting every positive element. We've already done most of the
work while implementing localisations:

```agda
PositiveΩ : Int → Ω
PositiveΩ x .∣_∣ = Positive x
PositiveΩ x .is-tr = hlevel 1

private
  module L = Loc ℤ-comm PositiveΩ record { has-1 = pos 0 ; has-* = *ℤ-positive }
```

<!--
```agda
  module ℤ = CRing ℤ-comm hiding (has-is-set ; magma-hlevel)

open Algebra.Ring.Localisation using (module Fraction) public

Fraction : Type
Fraction = Algebra.Ring.Localisation.Fraction Positive

open Frac ℤ-comm using (Inductive-≈)
open Explicit ℤ-comm
open Fraction renaming (num to ↑ ; denom to ↓) public
open L using (_≈_) renaming (module Fr to ≈) public
open Algebra.Ring.Localisation using (_/_[_]) public
```
-->

Strictly speaking, we are done: we could simply define $\bQ$ to be the
ring we just constructed. However, for the sake of implementation
hiding, we wrap it as a distinct type constructor. This lets consumers
of the type $\bQ$ forget that it's implemented as a localisation.

```agda
record Ratio : Type where
  no-eta-equality ; pattern
  constructor inc
  field
    unℚ : ⌞ L.S⁻¹R ⌟

toℚ : Fraction → Ratio
toℚ x = inc (inc x)

_+ℚ_ : Ratio → Ratio → Ratio
_+ℚ_ (inc x) (inc y) = inc (x L.+ₗ y)

_*ℚ_ : Ratio → Ratio → Ratio
_*ℚ_ (inc x) (inc y) = inc (x L.*ₗ y)

-ℚ_ : Ratio → Ratio
-ℚ_ (inc x) = inc (L.-ₗ x)
```

<!--
```agda
-- Note on the definitions of ℚ/the operations above: we want all the
-- algebraic operations over ℚ to be definitionally injective. This
-- means that every clause has to have a proper match and return a
-- constructor.
open Ratio public
```
-->

However, clients of this module *will* need the fact that $\bQ$ is a
quotient of the type of integer fractions. Therefore, we expose an
elimination principle, saying that to show a [[proposition]] everywhere
over $\bQ$, it suffices to do so at the fractions.

```agda
ℚ-elim-prop
  : ∀ {ℓ} {P : Ratio → Type ℓ} (pprop : ∀ x → is-prop (P x))
  → (f : ∀ x → P (toℚ x))
  → ∀ x → P x
ℚ-elim-prop pprop f (inc (inc x)) = f x
ℚ-elim-prop pprop f (inc (glue r@(x , y , _) i)) = is-prop→pathp (λ i → pprop (inc (glue r i))) (f x) (f y) i
ℚ-elim-prop pprop f (inc (squash x y p q i j)) =
  is-prop→squarep
    (λ i j → pprop (inc (squash x y p q i j)))
    (λ i → go (inc x)) (λ i → go (inc (p i))) (λ i → go (inc (q i))) (λ i → go (inc y))
    i j
  where go = ℚ-elim-prop pprop f
```

<!--
```agda
ℚ-rec
  : ∀ {ℓ} {P : Type ℓ} ⦃ _ : H-Level P 2 ⦄
  → (f : Fraction → P)
  → (∀ x y → x ≈ y → f x ≡ f y)
  → Ratio → P
ℚ-rec f p (inc x) = Coeq-rec f (λ (x , y , r) → p x y r) x
```
-->

Next, we show that sameness of fractions implies identity in $\bQ$, and
the converse is true as well:

```agda
abstract
  quotℚ : ∀ {x y} → x ≈ y → toℚ x ≡ toℚ y
  quotℚ p = ap Ratio.constructor (quot p)

  unquotℚ : ∀ {x y} → toℚ x ≡ toℚ y → x ≈ y
  unquotℚ p = ≈.effective (ap unℚ p)
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
from-same-rational : {x y : Fraction} → x ≈ y → x .↑ *ℤ y .↓ ≡ y .↑ *ℤ x .↓
from-same-rational {x / s [ s≠0 ]} {y / t [ t≠0 ]} p = case L.≈→≈' p of λ where
  u@(possuc u') (pos u') p → case *ℤ-is-zero u _ p of λ where
    (inl u=0)     → absurd (suc≠zero (pos-injective u=0))
    (inr xt-ys=0) → ℤ.zero-diff xt-ys=0

to-same-rational : {x y : Fraction} → x .↑ *ℤ y .↓ ≡ y .↑ *ℤ x .↓ → x ≈ y
to-same-rational {x / s [ s≠0 ]} {y / t [ t≠0 ]} p = L.inc 1 (pos 0) (sym (*ℤ-associative 1 x t) ∙∙ ap (1 *ℤ_) p ∙∙ *ℤ-associative 1 y s)

Dec-same-rational : (x y : Fraction) → Dec (x ≈ y)
Dec-same-rational f@(x / s [ _ ]) f'@(y / t [ _ ]) with x *ℤ t ≡? y *ℤ s
... | yes p = yes (to-same-rational p)
... | no xt≠ys = no λ p → xt≠ys (from-same-rational p)
```

<!--
```agda
private
  _≡ℚ?_ : (x y : ⌞ L.S⁻¹R ⌟) → Dec (x ≡ y)
  x ≡ℚ? y = Discrete-quotient L.Fraction-congruence Dec-same-rational .decide x y

instance
  Discrete-ℚ : Discrete Ratio
  Discrete-ℚ .decide (inc x) (inc y) with x ≡ℚ? y
  ... | yes p = yes (ap Ratio.constructor p)
  ... | no ¬p = no (¬p ∘ ap unℚ)
```
-->

<details>
<summary>
There are a number of other properties of $\bZ{\loc{\ne 0}}$ that we can
export as properties of $\bQ$; however, these are all trivial as above,
so we do not remark on them any further.
</summary>

```agda
_-ℚ_ : Ratio → Ratio → Ratio
(inc x) -ℚ (inc y) = inc (x L.+ₗ L.-ₗ y)

infixl 8 _+ℚ_ _-ℚ_
infixl 9 _*ℚ_
infix 10 -ℚ_

_/_ : (x y : Int) ⦃ _ : Positive y ⦄ → Ratio
_/_ x y ⦃ p ⦄ = toℚ (x / y [ p ])

infix 11 _/_

{-# DISPLAY Ratio.constructor (Coeq.inc (_/_[_] x y _)) = x / y #-}
{-# DISPLAY _/_ x (Int.pos 1) = x #-}

_/1 : Int → Ratio
x /1 = x / 1

instance
  H-Level-ℚ : ∀ {n} → H-Level Ratio (2 + n)
  H-Level-ℚ = basic-instance 2 (Discrete→is-set auto)

  Number-ℚ : Number Ratio
  Number-ℚ .Number.Constraint _ = ⊤
  Number-ℚ .Number.fromNat x = pos x /1

  Negative-ℚ : Negative Ratio
  Negative-ℚ .Negative.Constraint _ = ⊤
  Negative-ℚ .Negative.fromNeg 0 = 0
  Negative-ℚ .Negative.fromNeg (suc x) = negsuc x /1

  Inductive-ℚ
    : ∀ {ℓ ℓm} {P : Ratio → Type ℓ}
    → ⦃ _ : Inductive ((x : Fraction) → P (toℚ x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-ℚ ⦃ r ⦄ .Inductive.methods = r .Inductive.methods
  Inductive-ℚ ⦃ r ⦄ .Inductive.from f = ℚ-elim-prop (λ x → hlevel 1) (r .Inductive.from f)

abstract
  +ℚ-idl : ∀ x → 0 +ℚ x ≡ x
  +ℚ-idl (inc x) = ap inc (L.+ₗ-idl x)

  +ℚ-idr : ∀ x → x +ℚ 0 ≡ x
  +ℚ-idr (inc x) = ap Ratio.constructor (CRing.+-idr L.S⁻¹R)

  +ℚ-invl : ∀ x → (-ℚ x) +ℚ x ≡ 0
  +ℚ-invl (inc x) = ap Ratio.constructor (CRing.+-invl L.S⁻¹R {x})

  +ℚ-invr : ∀ x → x +ℚ (-ℚ x) ≡ 0
  +ℚ-invr (inc x) = ap Ratio.constructor (L.+ₗ-invr x)

  +ℚ-associative : ∀ x y z → x +ℚ (y +ℚ z) ≡ (x +ℚ y) +ℚ z
  +ℚ-associative (inc x) (inc y) (inc z) = ap inc (L.+ₗ-assoc x y z)

  +ℚ-commutative : ∀ x y → x +ℚ y ≡ y +ℚ x
  +ℚ-commutative (inc x) (inc y) = ap inc (L.+ₗ-comm x y)

  *ℚ-idl : ∀ x → 1 *ℚ x ≡ x
  *ℚ-idl (inc x) = ap inc (L.*ₗ-idl x)

  *ℚ-idr : ∀ x → x *ℚ 1 ≡ x
  *ℚ-idr (inc x) = ap Ratio.constructor (CRing.*-idr L.S⁻¹R)

  *ℚ-associative : ∀ x y z → x *ℚ (y *ℚ z) ≡ (x *ℚ y) *ℚ z
  *ℚ-associative (inc x) (inc y) (inc z) = ap inc (L.*ₗ-assoc x y z)

  *ℚ-commutative : ∀ x y → x *ℚ y ≡ y *ℚ x
  *ℚ-commutative (inc x) (inc y) = ap inc (L.*ₗ-comm x y)

  *ℚ-zerol : ∀ x → 0 *ℚ x ≡ 0
  *ℚ-zerol (inc x) = ap Ratio.constructor (CRing.*-zerol L.S⁻¹R {x})

  *ℚ-zeror : ∀ x → x *ℚ 0 ≡ 0
  *ℚ-zeror (inc x) = ap Ratio.constructor (CRing.*-zeror L.S⁻¹R {x})

  *ℚ-distribl : ∀ x y z → x *ℚ (y +ℚ z) ≡ x *ℚ y +ℚ x *ℚ z
  *ℚ-distribl (inc x) (inc y) (inc z) = ap Ratio.constructor (L.*ₗ-distribl x y z)

  *ℚ-distribr : ∀ x y z → (y +ℚ z) *ℚ x ≡ y *ℚ x +ℚ z *ℚ x
  *ℚ-distribr x y z = *ℚ-commutative (y +ℚ z) x ∙ *ℚ-distribl x y z ∙ ap₂ _+ℚ_ (*ℚ-commutative x y) (*ℚ-commutative x z)

+ℚ-monoid : is-monoid 0 _+ℚ_
+ℚ-monoid = record { has-is-semigroup = record { has-is-magma = record { has-is-set = hlevel 2 } ; associative = λ {x} {y} {z} → +ℚ-associative x y z } ; idl = +ℚ-idl _ ; idr = +ℚ-idr _ }

*ℚ-monoid : is-monoid 1 _*ℚ_
*ℚ-monoid = record { has-is-semigroup = record { has-is-magma = record { has-is-set = hlevel 2 } ; associative = λ {x} {y} {z} → *ℚ-associative x y z } ; idl = *ℚ-idl _ ; idr = *ℚ-idr _ }

ℚ-ring : CRing lzero
∣ ℚ-ring .fst ∣ = Ratio
ℚ-ring .fst .is-tr = hlevel 2
ℚ-ring .snd .CRing-on.has-ring-on = to-ring-on mk where
  open make-ring
  mk : make-ring Ratio
  mk .ring-is-set = hlevel 2
  mk .0R = 0
  mk .make-ring._+_ = _+ℚ_
  - mk = -ℚ_
  mk .+-idl = +ℚ-idl
  mk .+-invr = +ℚ-invr
  mk .+-assoc = +ℚ-associative
  mk .+-comm = +ℚ-commutative
  mk .1R = 1
  mk .make-ring._*_ = _*ℚ_
  mk .*-idl = *ℚ-idl
  mk .*-idr = *ℚ-idr
  mk .*-assoc = *ℚ-associative
  mk .*-distribl = *ℚ-distribl
  mk .*-distribr = *ℚ-distribr
ℚ-ring .snd .CRing-on.*-commutes = *ℚ-commutative _ _
```

</details>

## As a field

An important property of the ring $\bQ$ is that any nonzero rational
number is invertible. Since inverses are unique when they exist --- the
type of inverses is a proposition --- it suffices to show this at the
more concrete level of integer fractions.

```agda
inverseℚ : (x : Ratio) → x ≠ 0 → Σ[ y ∈ Ratio ] (x *ℚ y ≡ 1)
inverseℚ = ℚ-elim-prop is-p go where
  abstract
    is-p : (x : Ratio) → is-prop (x ≠ 0 → Σ[ y ∈ Ratio ] (x *ℚ y ≡ 1))
    is-p x = Π-is-hlevel 1 λ _ (y , p) (z , q) → Σ-prop-path! (monoid-inverse-unique *ℚ-monoid x y z (*ℚ-commutative y x ∙ p) q)

    rem₁ : ∀ x y → 1 *ℤ (x *ℤ y) *ℤ 1 ≡ 1 *ℤ (y *ℤ x)
    rem₁ x y = ap (_*ℤ 1) (*ℤ-onel (x *ℤ y))
      ∙ *ℤ-oner (x *ℤ y) ∙ *ℤ-commutative x y ∙ sym (*ℤ-onel (y *ℤ x))
```

This leaves us with three cases: either the fraction $x/y$ had a
denominator of zero, contradicting our assumption, or its numerator is
also nonzero (either positive or negative), so that we can form the
fraction $y/x$. It's then routine to show that $(x/y)(y/x) = 1$ holds in
$\bQ$.

```agda
  go : (x : Fraction) → toℚ x ≠ 0 → Σ[ y ∈ Ratio ] (toℚ x *ℚ y ≡ 1)
  go (posz / y [ _ ]) nz = absurd (nz (quotℚ (L.inc 1 decide! refl)))
  go (x@(possuc x') / y [ _ ]) nz = y / x , quotℚ (L.inc 1 decide! (rem₁ x y))
  go (x@(negsuc x') / y [ p ]) nz with y | p
  ... | possuc y | _ = negsuc y / possuc x' , quotℚ (L.inc 1 decide! (rem₁ (negsuc x') (negsuc y)))
  ... | negsuc y | _ = possuc y / possuc x' , quotℚ (L.inc 1 decide! (rem₁ x (possuc y)))
```

## Reduced fractions

We now show that the quotient defining $\bQ$ is [[*split*|split
quotient]]: integer fractions have a well-defined notion of *normal
form*, and similarity of fractions is equivalent to equality under
normalisation. The procedure we formalise is the familiar one, sending a
fraction $x/y$ to

$$
\frac{x \ndiv \gcd(x, y)}{y \ndiv \gcd(x, y)}
$$.

What remains is proving that this is actually a normalisation procedure,
which takes up the remainder of this module.

```agda
reduce-fraction : Fraction → Fraction
reduce-fraction (x / y [ p ]) = reduced module reduce where
  gcd[x,y] : GCD (abs x) (abs y)
  gcd[x,y] = Euclid.euclid (abs x) (abs y)
```

<!--
```agda
  open Σ gcd[x,y] renaming (fst to g) using () public
  open is-gcd (gcd[x,y] .snd)

  open Σ (∣→fibre gcd-∣l) renaming (fst to x/g ; snd to x/g*g=x) public
  open Σ (∣→fibre gcd-∣r) renaming (fst to y/g ; snd to y/g*g=y) public
```
-->

Our first obligation, to form the reduced fraction at all, is showing
that the denominator is non-zero. This is pretty easy: we know that $y$
is nonzero, so if $y \ndiv \gcd(x,y)$ were zero, we would have
$$y = \gcd(x, y) * (y \ndiv \gcd(x,y)) = \gcd(x,y) * 0 = 0$$,
which is a contradiction. A similar argument shows that $\gcd(x,y)$ is
itself nonzero, a fact we'll need later.

```agda
  rem₁ : y/g ≠ 0
  rem₁ y/g=0 with y/g | y/g=0 | y/g*g=y
  ... | zero  | y/g=0 | q = positive→nonzero p (abs-positive y (sym q))
  ... | suc n | y/g=0 | q = absurd (suc≠zero y/g=0)

  rem₂ : g ≠ 0
  rem₂ g=0 = positive→nonzero p (abs-positive y (sym (sym (*-zeror y/g) ∙ ap (y/g *_) (sym g=0) ∙ y/g*g=y)))
```

Finally, we must quickly mention the issue of signs. Since `gcd`{.Agda}
produces a natural number, we have to multiply it by the sign $\sgn(x)$
of $x$, to make sure signs are preserved. Note that the denominator must
be positive.

```agda
  reduced : Fraction
  reduced = assign (sign x) x/g / pos y/g [ pos-positive rem₁ ]
```

Finally, we can calculate that these fractions are similar.

```agda
  related : (x / y [ p ]) ≈ reduced
  related = L.inc (pos g) (pos-positive rem₂) $
    pos g *ℤ x *ℤ pos y/g               ≡⟨ solve 3 (λ x y z → x :* y :* z ≔ (z :* x) :* y) (pos g) x (pos y/g) refl ⟩
    (pos y/g *ℤ pos g) *ℤ x             ≡⟨ ap (_*ℤ x) (ap (assign pos) y/g*g=y) ⟩
    assign pos (abs y) *ℤ x             ≡⟨ ap₂ _*ℤ_ (assign-pos-positive y p) (sym (divides-*ℤ {n = x/g} {g} {x} (*-commutative g x/g ∙ x/g*g=x))) ⟩
    y *ℤ (pos g *ℤ assign (sign x) x/g) ≡⟨ solve 3 (λ y g x → y :* (g :* x) ≔ g :* x :* y) y (pos g) (assign (sign x) x/g) refl ⟩
    pos g ℤ.* assign (sign x) x/g ℤ.* y ∎
```

<!--
```agda
  coprime : is-gcd x/g y/g 1
  coprime .is-gcd.gcd-∣l = ∣-one
  coprime .is-gcd.gcd-∣r = ∣-one
  coprime .is-gcd.greatest {g'} p q with (p , α) ← ∣→fibre p | (q , β) ← ∣→fibre q =
    ∣-*-cancelr {g} {g'} {1} ⦃ nonzero→positive rem₂ ⦄ (∣-trans (gcd[x,y] .snd .is-gcd.greatest p1 p2) (subst (g ∣_) (sym (+-zeror g)) ∣-refl))
    where
      p1 : g' * g ∣ abs x
      p1 = fibre→∣ (p , *-associative p g' g ∙ ap (_* g) α ∙ x/g*g=x)

      p2 : g' * g ∣ abs y
      p2 = fibre→∣ (q , *-associative q g' g ∙ ap (_* g) β ∙ y/g*g=y)

```
-->

We'll now show that `reduce-fraction`{.Agda} respects similarity of
fractions. We show this by an intermediate lemma, which says that, given
a non-zero $s$ and a fraction $x/y$, we have
$$
\frac{xs \ndiv \gcd(xs, ys)}{ys \ndiv \gcd(xs, ys)} = \frac{x \ndiv \gcd(x, y)}{y \ndiv \gcd(x, y)}
$$,
as integer fractions (rather than rational numbers).

```agda
reduce-*r
  : ∀ x y s (p : Positive y) (q : Positive s)
  → reduce-fraction ((x *ℤ s) / (y *ℤ s) [ *ℤ-positive p q ])
  ≡ reduce-fraction (x / y [ p ])
reduce-*r x y s p q = Fraction-path (ap₂ assign sgn num) (ap Int.pos denom) where
```

<!--
```agda
  module m = reduce x y p
  module n = reduce (x *ℤ s) (y *ℤ s) (*ℤ-positive p q)

  open n renaming (x/g to xs/gcd ; y/g to ys/gcd) using ()
  open m renaming (x/g to x/gcd ; y/g to y/gcd) using ()

  instance
    _ : Data.Nat.Base.Positive (abs s)
    _ = nonzero→positive (λ p → positive→nonzero q (abs-positive s p))

    _ : Data.Nat.Base.Positive m.g
    _ = nonzero→positive m.rem₂

  gcdℤ : Int → Int → Nat
  gcdℤ x y = gcd (abs x) (abs y)
```
-->

The first observation is that $\gcd(xs, ys) = \gcd(x,y)s$, even when
absolute values are involved.^[Keep in mind that the `gcd`{.Agda}
function is defined over the naturals, and we're extending it to
integers by $\gcd(x,y) = \gcd(\abs{x}, \abs{y})$.]

```agda
  p1 : gcdℤ (x *ℤ s) (y *ℤ s) ≡ gcdℤ x y * abs s
  p1 = ap₂ gcd (abs-*ℤ x s) (abs-*ℤ y s) ∙ gcd-factor (abs x) (abs y) (abs s)
```

This implies that $$(xs \ndiv \gcd(xs, ys)) \gcd(x,y) s = x s$$, and,
because multiplication by $s$ is injective, this in turn implies that
$(xs \ndiv \gcd(xs, ys))\gcd(x, y)$ is also $x$. We conclude $(xs \ndiv
\gcd(xs, ys)) = (x \ndiv \gcd(x, y))$, since both sides multiply with
$\gcd(x, y)$ to $x$, and this multiplication is *also* injective.
Therefore, our numerators have the same absolute value.

```agda
  num' : xs/gcd * gcdℤ x y ≡ abs x
  num' = *-injr (abs s) (xs/gcd * m.g) (abs x) $
    xs/gcd * gcdℤ x y * abs s       ≡˘⟨ *-associative xs/gcd m.g (abs s) ⟩
    xs/gcd * (gcdℤ x y * abs s)     ≡˘⟨ ap (xs/gcd *_) p1 ⟩
    xs/gcd * gcdℤ (x *ℤ s) (y *ℤ s) ≡⟨ n.x/g*g=x ⟩
    abs (x *ℤ s)                    ≡⟨ abs-*ℤ x s ⟩
    abs x * abs s                   ∎

  num : xs/gcd ≡ x/gcd
  num = *-injr (gcdℤ x y) xs/gcd x/gcd (num' ∙ sym m.x/g*g=x)
```

We must still show that the resulting numerators have the same sign.
Fortunately, this boils down to a bit of algebra, plus the
hyper-specific fact that $\sgn(ab^2) = \sgn(a)$, whenever $b$ is
nonzero.^[Here, we're applying this lemma with $a = xy$ and $b = s$, and
we have assumed $s$ nonzero. The $\sgn$ function is not fun.]

```agda
  sgn : sign (x *ℤ s) ≡ sign x
  sgn = sign-*ℤ-positive x s q
```

A symmetric calculation shows that the denominators also have the same
absolute value, and, since they're both positive in the resulting
fraction, we're done.

```agda
  denom' : ys/gcd * gcdℤ x y ≡ abs y
  denom' = *-injr (abs s) (ys/gcd * m.g) (abs y) (sym (*-associative ys/gcd m.g (abs s)) ∙ sym (ap (ys/gcd *_) p1) ∙ n.y/g*g=y ∙ abs-*ℤ y s)

  denom : ys/gcd ≡ y/gcd
  denom = *-injr (gcdℤ x y) ys/gcd y/gcd (denom' ∙ sym m.y/g*g=y)
```

We can use this to show that `reduce-fraction`{.Agda} sends similar
fractions to *equal* normal forms: If $x/s \approx y/t$, we have $xt =
ys$, and we can calculate
$$
\frac{x \ndiv \gcd(x, s)}{s \ndiv \gcd(x, s)}
= \frac{xt \ndiv \gcd(xt, st)}{st \ndiv \gcd(xt, st)}
= \frac{ys \ndiv \gcd(ys, ts)}{ts \ndiv \gcd(ys, ts)}
= \frac{y \ndiv \gcd(y, t)}{t \ndiv \gcd(y, t)}
$$
using the previous lemma. Thus, by the general logic of [[split
quotients]], we conclude that $\bQ$ is equivalent to the set of reduced
integer fractions.

```agda
reduce-resp : (x y : Fraction) → x ≈ y → reduce-fraction x ≡ reduce-fraction y
reduce-resp f@(x / s [ s≠0 ]) f'@(y / t [ t≠0 ]) p =
  let
    st≠0 = *ℤ-positive s≠0 t≠0
    ts≠0 = *ℤ-positive t≠0 s≠0
  in
    reduce-fraction (x / s [ s≠0 ])                ≡⟨ sym (reduce-*r x s t s≠0 t≠0) ⟩
    reduce-fraction ((x *ℤ t) / (s *ℤ t) [ st≠0 ]) ≡⟨ ap reduce-fraction (Fraction-path {x = _ / _ [ st≠0 ]} {y = _ / _ [ ts≠0 ]} (from-same-rational p) (*ℤ-commutative s t)) ⟩
    reduce-fraction ((y *ℤ s) / (t *ℤ s) [ ts≠0 ]) ≡⟨ reduce-*r y t s t≠0 s≠0 ⟩
    reduce-fraction (y / t [ t≠0 ])                ∎

integer-frac-splits : is-split-congruence L.Fraction-congruence
integer-frac-splits = record
  { has-is-set = hlevel 2
  ; normalise  = reduce-fraction
  ; represents = elim! reduce.related
  ; respects   = reduce-resp
  }
```

<!--
```agda
private module split = is-split-congruence integer-frac-splits

reduceℚ : Ratio → Fraction
reduceℚ (inc x) = split.choose x

splitℚ : (x : Ratio) → fibre toℚ x
splitℚ (inc x) = record where
  fst = split.choose x
  snd = ap inc (split.splitting x .snd)

abstract
  reduce-injective : ∀ x y → reduceℚ x ≡ reduceℚ y → x ≡ y
  reduce-injective = elim! (λ x s s≠0 y t t≠0 p → quotℚ (split.reflects _ _ p))

common-denominator
  : ∀ n (fs : Fin n → Fraction) → Σ[ c ∈ Int ] Σ[ p ∈ Positive c ] Σ[ n ∈ (Fin n → Int) ] (∀ j → fs j ≈ (n j / c [ p ]))
common-denominator 0 _ = 1 , pos 0 , (λ ()) , (λ ())
common-denominator (suc sz) fs with (c , c≠0 , nums , prfs) ← common-denominator sz (fs ∘ fsuc) | inspect (fs fzero)
... | n / d [ d≠0 ] , prf = c' , c'≠0 , nums' , prfs' where
  c'   = d *ℤ c
  c'≠0 = *ℤ-positive d≠0 c≠0

  nums' : Fin (suc sz) → Int
  nums' i with fin-view i
  ... | zero  = n *ℤ c
  ... | suc n = nums n *ℤ d

  abstract
    prfs' : (n : Fin (suc sz)) → fs n ≈ (nums' n / c' [ c'≠0 ])
    prfs' i with fin-view i
    ... | zero  = ≈.reflᶜ' prf ≈.∙ᶜ L.inc c c≠0 (solve 3 (λ c n d → c :* n :* (d :* c) ≔ c :* (n :* c) :* d) c n d refl)
    ... | suc n = prfs n ≈.∙ᶜ L.inc d d≠0 (solve 3 (λ c n d → d :* n :* (d :* c) ≔ d :* (n :* d) :* c) c (nums n) d refl)

-- Induction principle for n-tuples of rational numbers which reduces to
-- the case of n fractions /with the same denominator/. The type is
-- pretty noisy since it uses the combinators for finite products, but
-- it specialises at concrete n to what you would expect, e.g.
--
--    ℚ-elim-propⁿ 2
--      : ∀ {P : ℚ → ℚ → Prop}
--      → (∀ d (p : Positive d) a b → P (a / d) (b / d))
--      → ∀ a b → P a b
--
-- This is useful primarily when dealing with the order, since
-- a / d ≤ b / d is just a ≤ b. Algebraic properties of the rationals
-- don't generally get any easier by assuming a common denominator.

ℚ-elim-propⁿ
  : ∀ (n : Nat) {ℓ} {P : Arrᶠ {n = n} (λ _ → Ratio) (Type ℓ)}
  → ⦃ _ : {as : Πᶠ (λ i → Ratio)} → H-Level (applyᶠ P as) 1 ⦄
  → ( (d : Int) ⦃ p : Positive d ⦄
    → ∀ᶠ n (λ i → Int) (λ as → applyᶠ P (mapₚ (λ i n → toℚ (n / d [ p ])) as)))
  → ∀ᶠ n (λ _ → Ratio) λ as → applyᶠ P as

ℚ-elim-propⁿ n {P = P} work = curry-∀ᶠ go where abstract
  reps : ∀ n → (qs : Fin n → Ratio) → ∥ ((i : Fin n) → fibre toℚ (qs i)) ∥
  reps n qs = finite-choice n (λ i → ℚ-elim-prop {P = λ x → ∥ fibre toℚ x ∥} (λ _ → squash) (λ x → inc (x , refl)) (qs i))

  go : (as : Πᶠ (λ i → Ratio)) → applyᶠ P as
  go as = ∥-∥-out! do
    fracs' ← reps _ (indexₚ as)

    let
      fracs : Fin n → Fraction
      fracs i = fracs' i .fst

      same : (i : Fin n) → toℚ (fracs i) ≡ indexₚ as i
      same i = fracs' i .snd

    (d , d≠0 , nums , same') ← pure (common-denominator _ fracs)

    let
      rats : Πᶠ (λ i → Ratio)
      rats = mapₚ (λ i n → toℚ (n / d [ d≠0 ])) (tabulateₚ nums)

      p₀ : applyᶠ P rats
      p₀ = apply-∀ᶠ (work d ⦃ d≠0 ⦄) (tabulateₚ nums)

      rats=as : rats ≡ as
      rats=as = extₚ λ i →
        indexₚ-mapₚ (λ i n → toℚ (n / d [ d≠0 ])) (tabulateₚ nums) i
        ∙∙ ap (λ e → toℚ (e / d [ d≠0 ])) (indexₚ-tabulateₚ nums i)
        ∙∙ sym (quotℚ (same' i)) ∙ same i

    pure (subst (applyᶠ P) rats=as p₀)

same-frac : Fraction → Fraction → Prop lzero
same-frac f@record{} g@record{} = el! (f .↑ *ℤ g .↓ ≡ g .↑ *ℤ f .↓)

private
  eqℚ : Ratio → Ratio → Prop lzero
  eqℚ (inc x) (inc y) = Coeq-rec₂ (hlevel 2) same-frac
    (λ { f@(x / s [ p ]) (g@(y / t [ q ]) , h@(z / u [ r ]) , α) → n-ua (prop-ext!
      (λ β → from-same-rational {h} {f} (≈.symᶜ α ≈.∙ᶜ to-same-rational β))
      (λ β → from-same-rational {g} {f} (α ≈.∙ᶜ to-same-rational β))) })
    (λ { f@(x / s [ p ]) (g@(y / t [ q ]) , h@(z / u [ r ]) , α) → n-ua (prop-ext!
      (λ β → from-same-rational {f} {h} (to-same-rational β ≈.∙ᶜ α))
      (λ β → from-same-rational {f} {g} (to-same-rational β ≈.∙ᶜ ≈.symᶜ α))) })
    x y

open Extensional

instance
  Extensional-ℚ : Extensional Ratio lzero
  Extensional-ℚ .Pathᵉ x y = ⌞ eqℚ x y ⌟
  Extensional-ℚ .reflᵉ = ℚ-elim-prop (λ _ → hlevel 1) λ { record{} → refl }
  Extensional-ℚ .idsᵉ .to-path {a} {b} = go a b where
    go : ∀ a b → ⌞ eqℚ a b ⌟ → a ≡ b
    go = ℚ-elim-propⁿ 2 (λ d a b p → quotℚ (to-same-rational p))
  Extensional-ℚ .idsᵉ .to-path-over p = prop!

record Nonzero (x : Ratio) : Type where
  constructor inc
  field
    lower : x ≠ 0

instance
  H-Level-Nonzero : ∀ {x n} → H-Level (Nonzero x) (suc n)
  H-Level-Nonzero = prop-instance λ _ _ → refl

open Nonzero

abstract
  from-nonzero : ∀ {x} ⦃ p : Nonzero x ⦄ → x ≠ 0
  from-nonzero ⦃ inc α ⦄ p = absurd (α p)

  from-nonzero-frac : ∀ {x y} {p : Positive y} → Nonzero (toℚ (x / y [ p ])) → x ≠ 0
  from-nonzero-frac (inc α) p = absurd (α (quotℚ (to-same-rational (*ℤ-oner _ ∙ p))))

  to-nonzero-frac : ∀ {x y} {p : Positive y} → x ≠ 0 → Nonzero (toℚ (x / y [ p ]))
  to-nonzero-frac p = inc λ α → p (sym (*ℤ-oner _) ∙ from-same-rational (unquotℚ α))

instance
  Nonzero-neg : ∀ {x d} {p : Positive d} → Nonzero (toℚ (negsuc x / d [ p ]))
  Nonzero-neg = inc (λ p → absurd (negsuc≠pos (from-same-rational (unquotℚ p))))

  Nonzero-pos : ∀ {x d} {p : Positive d} ⦃ _ : Positive x ⦄ → Nonzero (toℚ (x / d [ p ]))
  Nonzero-pos {.(possuc x)} ⦃ pos x ⦄ = inc (λ p → absurd (suc≠zero (pos-injective (from-same-rational (unquotℚ p)))))
  {-# OVERLAPPABLE Nonzero-pos #-}

-- Since we want invℚ to be injective as well, we re-wrap the result on
-- the RHS, to make sure the clause is headed by a constructor.
invℚ : (x : Ratio) ⦃ p : Nonzero x ⦄ → Ratio
invℚ (inc x) ⦃ inc α ⦄ = inc (unℚ (inverseℚ (inc x) (λ p → absurd (α p)) .fst))

*ℚ-invr : {x : Ratio} {p : Nonzero x} → x *ℚ invℚ x ⦃ p ⦄ ≡ 1
*ℚ-invr {inc x} {inc α} with inverseℚ (inc x) (λ p → absurd (α p))
... | (inc x , p) = p

-ℚ-def : ∀ x y → x +ℚ (-ℚ y) ≡ x -ℚ y
-ℚ-def (inc x) (inc y) = refl

_/ℚ_ : (x y : Ratio) ⦃ p : Nonzero y ⦄ → Ratio
inc x /ℚ inc y = inc x *ℚ invℚ (inc y)

abstract
  from-same-denom : ∀ {x y d} ⦃ p : Positive d ⦄ → x / d ≡ y / d → x ≡ y
  from-same-denom {x} {y} {d} p = *ℤ-injectiver d x y (positive→nonzero auto) (from-same-rational (unquotℚ p))
```
-->
