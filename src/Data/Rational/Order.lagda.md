<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver

open import Data.Set.Coequaliser hiding (_/_)
open import Data.Rational.Base
open import Data.Int.Base hiding (Positive ; H-Level-Positive ; Dec-Positive)
open import Data.Dec

open import Order.Instances.Int
open import Order.Reasoning Int-poset using (_=⟨_⟩_ ; _≤⟨_⟩_ ; _=˘⟨_⟩_ ; _≤∎)

import Data.Int.Properties as ℤ
import Data.Int.Order as ℤ
import Data.Int.Base as ℤ
```
-->

```agda
module Data.Rational.Order where
```

<!--
```agda
open Explicit ℤ-comm
```
-->

# Ordering on rationals

The field $\bQ$ of [[rational numbers]] inherits a [[partial order]]
from the ring of integers $\bZ$, defining the relation
$$
\frac{x}{s} \le \frac{y}{t}
$$
to be $xt \le ys$. As usual, we define this first at the level of
fractions, then prove that it extends to the quotient $\bQ$.

```agda
_≤ᶠ_ : Fraction → Fraction → Type
(x / s [ _ ]) ≤ᶠ (y / t [ _ ]) = (x *ℤ t) ℤ.≤ (y *ℤ s)
```

The easiest way to show this is transitivity at the level of fractions,
since it will follow directly from the definition that $q \approx q'$
implies $q \le q'$. We can then prove that $q \le q'$ is invariant under
$\approx$, on either side, by appealing to transitivity. The proof is
not complicated, just annoying:

```agda
≤ᶠ-refl' : ∀ {x y} → x ≈ y → x ≤ᶠ y
≤ᶠ-refl' {x@record{}} {y@record{}} p = ℤ.≤-refl' (from-same-rational p)

≤ᶠ-trans : ∀ x y z → x ≤ᶠ y → y ≤ᶠ z → x ≤ᶠ z
≤ᶠ-trans (x / s [ pos s' ]) (y / t [ pos t' ]) (z / u [ pos u' ]) α β =
  (ℤ.*ℤ-cancel-≤r {t} $
    x *ℤ u *ℤ t   =⟨ solve 3 (λ x u t → x :* u :* t ≔ x :* t :* u) x u t refl ⟩
    x *ℤ t *ℤ u   ≤⟨ ℤ.*ℤ-preserves-≤r u α ⟩
    y *ℤ s *ℤ u   =⟨ solve 3 (λ y s u → y :* s :* u ≔ y :* u :* s) y s u refl ⟩
    y *ℤ u *ℤ s   ≤⟨ ℤ.*ℤ-preserves-≤r s β ⟩
    z *ℤ t *ℤ s   =⟨ solve 3 (λ z t s → z :* t :* s ≔ z :* s :* t) z t s refl ⟩
    z *ℤ s *ℤ t   ≤∎)
```

<details>
<summary>
We can then lift this to a family of [[propositions]] over $\bQ \times
\bQ$. The strategy for showing it respects the quotient is as outlined
above, so we'll leave this in a `<details>`{.html} block.
</summary>

```agda
private
  leℚ : ℚ → ℚ → Prop lzero
  leℚ (inc x) (inc y) =
    Coeq-rec₂ (hlevel 2) work
      (λ a (x , y , r) → r2 x y a r)
      (λ a (x , y , r) → r1 a x y r) x y
    where
    work : Fraction → Fraction → Prop lzero
    ∣ work x y ∣ = x ≤ᶠ y
    work record{} record{} .is-tr = hlevel 1

    r1 : ∀ u x y → x ≈ y → work u x ≡ work u y
    r1 u@record{} x@record{} y@record{} p' = n-ua (prop-ext!
      (λ α → ≤ᶠ-trans u x y α (≤ᶠ-refl' p'))
      (λ α → ≤ᶠ-trans u y x α (≤ᶠ-refl' (≈.symᶜ p'))))

    r2 : ∀ x y u → x ≈ y → work x u ≡ work y u
    r2 u@record{} x@record{} y@record{} p' = n-ua (prop-ext!
      (λ α → ≤ᶠ-trans x u y (≤ᶠ-refl' (≈.symᶜ p')) α)
      (λ α → ≤ᶠ-trans u x y (≤ᶠ-refl' p') α))
```

</details>

We define the type family `_≤_`{.Agda} as a record type, wrapping
`orderℚ`{.Agda}, to help out type inference: `orderℚ`{.Agda} is a pretty
nasty definition, whereas an application of a record name is always a
normal form.

```agda
record _≤_ (x y : ℚ) : Type where
  constructor inc
  field
    lower : ⌞ leℚ x y ⌟
```

<!--
```agda
open _≤_
unquoteDecl H-Level-≤ = declare-record-hlevel 1 H-Level-≤ (quote _≤_)
```
-->

By lifting our proofs about `_≤ᶠ_`{.Agda} through this record type, we
can prove that the ordering on the rational numbers is decidable,
reflexive, transitive, and antisymmetric.

```agda
≤-dec : ∀ x y → Dec (x ≤ y)
≤-dec = elim! go where
  go : ∀ x y → Dec (toℚ x ≤ toℚ y)
  go x@record{} y@record{} with holds? ((↑ x *ℤ ↓ y) ℤ.≤ (↑ y *ℤ ↓ x))
  ... | yes p = yes (inc p)
  ... | no ¬p = no (¬p ∘ lower)

instance
  Dec-≤ : ∀ {x y} → Dec (x ≤ y)
  Dec-≤ {x} {y} = ≤-dec x y

abstract
  toℚ≤ : ∀ {x y} → (↑ x *ℤ ↓ y) ℤ.≤ (↑ y *ℤ ↓ x) → toℚ x ≤ toℚ y
  toℚ≤ {record{}} {record{}} p = inc p

  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl {x} = work x where
    work : ∀ x → x ≤ x
    work = elim! λ f → toℚ≤ ℤ.≤-refl

  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} = work x y z where
    work : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    work = elim! λ x y z p q → inc (≤ᶠ-trans x y z (p .lower) (q .lower))

  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym {x} {y} = work x y where
    work : ∀ x y → x ≤ y → y ≤ x → x ≡ y
    work = elim! λ where
      x@record{} y@record{} p q → quotℚ (to-same-rational (ℤ.≤-antisym (p .lower) (q .lower)))
```

## Algebraic properties

We can also show that the ordering on $\bQ$ behaves well with respect to
its algebraic structure. For example, the addition function is monotone
in both arguments, and division by a positive integer preserves the
order.

```agda
  common-denominator-≤ : ∀ {x y d} (p : ℤ.Positive d) → x ℤ.≤ y → toℚ (x / d [ p ]) ≤ toℚ (y / d [ p ])
  common-denominator-≤ {d = d} (pos _) p = inc (ℤ.*ℤ-preserves-≤r d p)

  +ℚ-preserves-≤ : ∀ x y a b → x ≤ y → a ≤ b → (x +ℚ a) ≤ (y +ℚ b)
  +ℚ-preserves-≤ = ℚ-elim-propⁿ 4 λ d d≠0 x y a b (inc p) (inc q) →
    common-denominator-≤ (ℤ.*ℤ-positive d≠0 d≠0) $
      x *ℤ d +ℤ a *ℤ d ≤⟨ ℤ.+ℤ-preserves-≤r (a *ℤ d) _ _ p ⟩
      y *ℤ d +ℤ a *ℤ d ≤⟨ ℤ.+ℤ-preserves-≤l (y *ℤ d) _ _ q ⟩
      y *ℤ d +ℤ b *ℤ d ≤∎

  *ℚ-nonnegative : ∀ x y → 0 ≤ x → 0 ≤ y → 0 ≤ (x *ℚ y)
  *ℚ-nonnegative = ℚ-elim-propⁿ 2 λ d d≠0 x y (inc p) (inc q) → inc (ℤ.≤-trans
    (ℤ.*ℤ-nonnegative
      (ℤ.≤-trans p (ℤ.≤-refl' (ℤ.*ℤ-oner x)))
      (ℤ.≤-trans q (ℤ.≤-refl' (ℤ.*ℤ-oner y))))
    (ℤ.≤-refl' (sym (ℤ.*ℤ-oner (x *ℤ y)))))
```

## Positivity

We can also lift the notion of positivity from the integers to the
rational numbers. A fraction is positive if its numerator is positive.

```agda
private
  positiveℚ : ℚ → Prop lzero
  positiveℚ (inc x) = Coeq-rec (λ f → el! (ℤ.Positive (↑ f))) (λ (x , y , p) → r x y p) x where
    r : ∀ x y → x ≈ y → el! (ℤ.Positive (↑ x)) ≡ el! (ℤ.Positive (↑ y))
    r (x / s [ ps ]) (y / t [ pt ]) r with r ← from-same-rational r = n-ua (prop-ext!
      (λ px → ℤ.*ℤ-positive-cancel ps (subst ℤ.Positive (r ∙ ℤ.*ℤ-commutative y s) (ℤ.*ℤ-positive px pt)))
      λ py → ℤ.*ℤ-positive-cancel pt (subst ℤ.Positive (sym r ∙ ℤ.*ℤ-commutative x t) (ℤ.*ℤ-positive py ps)))

record Positive (q : ℚ) : Type where
  constructor inc
  field
    lower : ⌞ positiveℚ q ⌟
```

<!--
```agda
open Positive

unquoteDecl H-Level-Positive = declare-record-hlevel 1 H-Level-Positive (quote Positive)

instance
  Dec-Positive : ∀ {x} → Dec (Positive x)
  Dec-Positive {x} with (r@(n / d [ p ]) , q) ← splitℚ x | holds? (ℤ.Positive n)
  ... | yes p = yes (subst Positive q (inc (recover p)))
  ... | no ¬p = no λ x → case subst Positive (sym q) x of λ (inc p) → ¬p p

  Positive-pos : ∀ {x s p} → Positive (toℚ (possuc x / s [ p ]))
  Positive-pos = inc (pos _)
```
-->

This has the expected interaction with the ordering and the algebraic
operations.

```agda
nonnegative-nonzero→positive : ∀ {x} → 0 ≤ x → x ≠ 0 → Positive x
nonnegative-nonzero→positive = work _ where
  work : ∀ x → 0 ≤ x → x ≠ 0 → Positive x
  work = ℚ-elim-propⁿ 1 λ where
    d p posz (inc q) r → absurd (r (ext refl))
    d p (possuc x) (inc q) r → inc (pos x)

*ℚ-positive : ∀ {x y} → Positive x → Positive y → Positive (x *ℚ y)
*ℚ-positive = work _ _ where
  work : ∀ x y → Positive x → Positive y → Positive (x *ℚ y)
  work = ℚ-elim-propⁿ 2 λ d p a b (inc x) (inc y) → inc (ℤ.*ℤ-positive x y)

+ℚ-positive : ∀ {x y} → Positive x → Positive y → Positive (x +ℚ y)
+ℚ-positive = work _ _ where
  work : ∀ x y → Positive x → Positive y → Positive (x +ℚ y)
  work = ℚ-elim-propⁿ 2 λ d p a b (inc x) (inc y) → inc (ℤ.+ℤ-positive (ℤ.*ℤ-positive x p) (ℤ.*ℤ-positive y p))
```
