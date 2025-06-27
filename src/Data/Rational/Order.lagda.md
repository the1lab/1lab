<!--
```agda
open import 1Lab.Prelude

open import Algebra.Ring.Commutative
open import Algebra.Ring.Solver

open import Data.Rational.Reflection
open import Data.Set.Coequaliser hiding (_/_)
open import Data.Sum.Properties
open import Data.Rational.Base
open import Data.Int.Base hiding (Positive ; H-Level-Positive ; Dec-Positive)
open import Data.Sum.Base
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

infix 7 _<_ _≤ᶠ_
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
  leℚ : Ratio → Ratio → Prop lzero
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
record _≤_ (x y : Ratio) : Type where
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

instance
  Dec-≤ : ∀ {x y} → Dec (x ≤ y)
  Dec-≤ {inc x} {inc y} = elim! {P = λ x → ∀ y → Dec (Ratio.inc x ≤ inc y)} go x y where
    go : ∀ x y → Dec (toℚ x ≤ toℚ y)
    go x@record{} y@record{} with holds? ((↑ x *ℤ ↓ y) ℤ.≤ (↑ y *ℤ ↓ x))
    ... | yes p = yes (inc p)
    ... | no ¬p = no (¬p ∘ lower)

  ≤-from : ∀ {x y} ⦃ p : (↑ x *ℤ ↓ y) ℤ.≤ (↑ y *ℤ ↓ x) ⦄ → toℚ x ≤ toℚ y
  ≤-from {record{}} {record{}} ⦃ p ⦄ = inc p

abstract
  toℚ≤ : ∀ {x y} → (↑ x *ℤ ↓ y) ℤ.≤ (↑ y *ℤ ↓ x) → toℚ x ≤ toℚ y
  toℚ≤ {record{}} {record{}} p = inc p

  ≤-refl    : ∀ {x} → x ≤ x
  ≤-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

  unquoteDef ≤-refl ≤-trans ≤-antisym = do
    by-elim-ℚ ≤-refl λ d x → inc ℤ.≤-refl

    by-elim-ℚ ≤-trans λ d x y z (inc p) (inc q) → inc
      (≤ᶠ-trans (x / d [ auto ]) (y / d [ auto ]) (z / d [ auto ]) p q)

    by-elim-ℚ ≤-antisym λ d x y (inc α) (inc β) →
      quotℚ (to-same-rational (ℤ.≤-antisym α β))

  ≤-refl' : ∀ {x y} (p : x ≡ y) → x ≤ y
  ≤-refl' {x} p = transport (λ i → x ≤ p i) ≤-refl
```

## Algebraic properties

We can also show that the ordering on $\bQ$ behaves well with respect to
its algebraic structure. For example, the addition function is monotone
in both arguments, and division by a positive integer preserves the
order.

```agda
  common-denominator-≤ : ∀ {x y d} (p : ℤ.Positive d) → x ℤ.≤ y → toℚ (x / d [ p ]) ≤ toℚ (y / d [ p ])
  common-denominator-≤ {d = d} (pos _) p = inc (ℤ.*ℤ-preserves-≤r d p)

  +ℚ-preserves-≤   : ∀ {x y a b} → x ≤ y → a ≤ b → (x +ℚ a) ≤ (y +ℚ b)
  *ℚ-nonnegative   : ∀ {x y} → 0 ≤ x → 0 ≤ y → 0 ≤ (x *ℚ y)
  invℚ-nonnegative : ∀ {x} ⦃ p : Nonzero x ⦄ → 0 ≤ x → 0 ≤ (invℚ x ⦃ p ⦄)

  unquoteDef +ℚ-preserves-≤ *ℚ-nonnegative invℚ-nonnegative = do

    by-elim-ℚ +ℚ-preserves-≤ λ d x y a b (inc p) (inc q) →
      common-denominator-≤ (ℤ.*ℤ-positive auto auto) $
        x *ℤ d +ℤ a *ℤ d ≤⟨ ℤ.+ℤ-preserves-≤r (a *ℤ d) _ _ p ⟩
        y *ℤ d +ℤ a *ℤ d ≤⟨ ℤ.+ℤ-preserves-≤l (y *ℤ d) _ _ q ⟩
        y *ℤ d +ℤ b *ℤ d ≤∎

    by-elim-ℚ *ℚ-nonnegative λ d x y (inc p) (inc q) → inc
      (ℤ.≤-trans
        (ℤ.*ℤ-nonnegative
          (ℤ.≤-trans p (ℤ.≤-refl' (ℤ.*ℤ-oner x)))
          (ℤ.≤-trans q (ℤ.≤-refl' (ℤ.*ℤ-oner y))))
        (ℤ.≤-refl' (sym (ℤ.*ℤ-oner (x *ℤ y)))))

    by-elim-ℚ invℚ-nonnegative λ where
      (possuc x) posz ⦃ inc nz ⦄ z → absurd (nz (quotℚ (to-same-rational refl)))
      (possuc x) (possuc y) z → inc (ℤ.pos≤pos 0≤x)

  /ℚ-nonnegative : ∀ {x y} ⦃ p : Nonzero y ⦄ → 0 ≤ x → 0 ≤ y → 0 ≤ (x /ℚ y)
  /ℚ-nonnegative {inc x} {inc y} a b = *ℚ-nonnegative a (invℚ-nonnegative {inc y} b)
```

## Positivity

We can also lift the notion of positivity from the integers to the
rational numbers. A fraction is positive if its numerator is positive.

```agda
private
  positiveℚ : Ratio → Prop lzero
  positiveℚ (inc x) = Coeq-rec (λ f → el! (ℤ.Positive (↑ f))) (λ (x , y , p) → r x y p) x where
    r : ∀ x y → x ≈ y → el! (ℤ.Positive (↑ x)) ≡ el! (ℤ.Positive (↑ y))
    r (x / s [ ps ]) (y / t [ pt ]) r with r ← from-same-rational r = n-ua (prop-ext!
      (λ px → ℤ.*ℤ-positive-cancel ps (subst ℤ.Positive (r ∙ ℤ.*ℤ-commutative y s) (ℤ.*ℤ-positive px pt)))
      λ py → ℤ.*ℤ-positive-cancel pt (subst ℤ.Positive (sym r ∙ ℤ.*ℤ-commutative x t) (ℤ.*ℤ-positive py ps)))

record Positive (q : Ratio) : Type where
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
  ... | no ¬p = no λ x → absurd (case subst Positive (sym q) x of λ (inc p) → ¬p p)

  Positive-pos : ∀ {x s p} → Positive (toℚ (possuc x / s [ p ]))
  Positive-pos = inc (pos _)
```
-->

This has the expected interaction with the ordering and the algebraic
operations.

```agda
nonnegative-nonzero→positive : ∀ {x} → 0 ≤ x → x ≠ 0 → Positive x
positive→nonzero : ∀ {x} → Positive x → x ≠ 0
positive→nonnegative : ∀ {x} → Positive x → 0 ≤ x

unquoteDef nonnegative-nonzero→positive positive→nonzero positive→nonnegative = do
  by-elim-ℚ nonnegative-nonzero→positive λ where
    d posz (inc q) r → absurd (r (ext refl))
    d (possuc x) (inc q) r → inc (pos x)

  by-elim-ℚ positive→nonzero λ where
    d a (inc α) β → ℤ.positive→nonzero α (sym (ℤ.*ℤ-oner a) ∙ from-same-rational (unquotℚ β))

  by-elim-ℚ positive→nonnegative λ where
    d a (inc α) → inc (ℤ.≤-trans (ℤ.positive→nonnegative α) (ℤ.≤-refl' (sym (ℤ.*ℤ-oner a))))
```

# The strict order on rationals

With a bit more effort, we can also lift the strict ordering on the
integers to the rationals. The definitions end up being pretty much the
same as for lifting the partial order! We start by defining it on
fractions, then showing that it respects the quotient on both sides ---
we can't use transitivity and reflexivity like we did above,
unfortunately.

```agda
_<ᶠ_ : Fraction → Fraction → Type
(x / s [ _ ]) <ᶠ (y / t [ _ ]) = (x *ℤ t) ℤ.< (y *ℤ s)

<ᶠ-respr : ∀ {x y f} → x ≈ y → f <ᶠ y → f <ᶠ x
<ᶠ-respr {x / s [ p ]} {y / t [ q ]} {z / u [ r ]} xt~ys α = ℤ.*ℤ-cancel-<r {t} ⦃ q ⦄ $
  ℤ.≤-<-trans
    (ℤ.≤-refl' (solve 3 (λ z s t → z :* s :* t ≔ (z :* t) :* s) z s t refl))
    (ℤ.<-≤-trans (ℤ.*ℤ-preserves-<r s ⦃ p ⦄ α) (ℤ.≤-refl'
      ( solve 3 (λ y u s → y :* u :* s ≔ y :* s :* u) y u s refl
      ∙ ap (_*ℤ u) (sym (from-same-rational xt~ys))
      ∙ solve 3 (λ x t u → x :* t :* u ≔ x :* u :* t) x t u refl)))

<ᶠ-respl : ∀ {x y f} → x ≈ y → x <ᶠ f → y <ᶠ f
<ᶠ-respl {x / s [ p ]} {y / t [ q ]} {z / u [ r ]} xt~ys α = ℤ.*ℤ-cancel-<l {s} ⦃ p ⦄ $
  ℤ.≤-<-trans
    (ℤ.≤-refl'
      ( solve 3 (λ s y u → s :* (y :* u) ≔ (y :* s) :* u) s y u refl
      ∙ ap (_*ℤ u) (sym (from-same-rational xt~ys))
      ∙ solve 3 (λ x t u → x :* t :* u ≔ x :* u :* t) x t u refl))
    (ℤ.<-≤-trans (ℤ.*ℤ-preserves-<r t ⦃ q ⦄ α)
      (ℤ.≤-refl' (solve 3 (λ z s t → (z :* s) :* t ≔ s :* (z :* t)) z s t refl)))
```

<details>
<summary>Having gotten the bulk of the construction out of the way, we
can lift it to a type family over pairs of rationals, and do the same
dance as to make this into something definitionally injective.</summary>

```agda
private
  ltℚ : Ratio → Ratio → Prop lzero
  ltℚ (inc x) (inc y) = Coeq-rec₂ (hlevel 2) work (λ u (x , y , r) → r2 x y u r) (λ u (x , y , r) → r1 u x y r) x y where
    work : Fraction → Fraction → Prop lzero
    ∣ work x y ∣ = x <ᶠ y
    work record{} record{} .is-tr = hlevel 1

    r1 : ∀ u x y → x ≈ y → work u x ≡ work u y
    r1 u@record{} x@record{} y@record{} p' = n-ua (prop-ext!
      (λ α → <ᶠ-respr {y} {x} {u} (≈.symᶜ p') α)
      (λ α → <ᶠ-respr {x} {y} {u} p' α))

    r2 : ∀ x y u → x ≈ y → work x u ≡ work y u
    r2 x@record{} y@record{} u@record{} p' = n-ua (prop-ext!
      (λ α → <ᶠ-respl {x} {y} {u} p' α)
      (λ α → <ᶠ-respl {y} {x} {u} (≈.symᶜ p') α))

record _<_ (x y : Ratio) : Type where
  constructor inc
  field
    lower : ⌞ ltℚ x y ⌟

open _<_
unquoteDecl H-Level-< = declare-record-hlevel 1 H-Level-< (quote _<_)
```

</details>

As before, everything we want to show about strict inequality on the
rationals follows by lifting the analogous facts from the integers,
where we're free to assume any set of related rationals has the same
denominator.

```agda
instance
  Dec-< : ∀ {x y} → Dec (x < y)
  Dec-< {inc x} {inc y} = elim! {P = λ x → ∀ y → Dec (inc x < inc y)} go x y where
    go : ∀ x y → Dec (toℚ x < toℚ y)
    go x@record{} y@record{} with holds? ((↑ x *ℤ ↓ y) ℤ.< (↑ y *ℤ ↓ x))
    ... | yes p = yes (inc p)
    ... | no ¬p = no (¬p ∘ lower)

abstract
  toℚ< : ∀ {x y} → (↑ x *ℤ ↓ y) ℤ.< (↑ y *ℤ ↓ x) → toℚ x < toℚ y
  toℚ< {record{}} {record{}} p = inc p

  common-denom-< : ∀ {x y d} ⦃ _ : ℤ.Positive d ⦄ → x ℤ.< y → (x / d) < (y / d)
  common-denom-< {x} {y} {d} p = inc (ℤ.*ℤ-preserves-<r {x} {y} d p)

  <-common-denom : ∀ {x y d} ⦃ _ : ℤ.Positive d ⦄ → (x / d) < (y / d) → x ℤ.< y
  <-common-denom {x} {y} {d} (inc p) = ℤ.*ℤ-cancel-<r {d} {x} {y} p

  <-irrefl     : ∀ {x y} → x ≡ y → ¬ x < y
  <-trans      : ∀ {x y z} → x < y → y < z → x < z
  <-weaken     : ∀ {x y} → x < y → x ≤ y
  ≤-strengthen : ∀ {x y} → x ≤ y → (x ≡ y) ⊎ (x < y)

  private instance
    hl-str : ∀ {x y} → H-Level ((x ≡ y) ⊎ (x < y)) 1
    hl-str = prop-instance (disjoint-⊎-is-prop (hlevel 1) (hlevel 1) λ (x , y) → <-irrefl x y)
    {-# OVERLAPPING hl-str #-}

  unquoteDef <-irrefl <-trans <-weaken ≤-strengthen = do
    by-elim-ℚ <-irrefl λ d x y p a →
      ℤ.<-irrefl (from-same-denom p) (<-common-denom a)

    by-elim-ℚ <-trans λ d x y z p q →
      common-denom-< (ℤ.<-trans (<-common-denom p) (<-common-denom q))

    by-elim-ℚ <-weaken λ d x y (inc p) → inc (ℤ.<-weaken p)

    by-elim-ℚ ≤-strengthen λ d x y (inc p) → case ℤ.≤-strengthen p of λ where
      (inl dx=dy) → inl (quotℚ (to-same-rational dx=dy))
      (inr dx<dy) → inr (inc dx<dy)

  <-≤-trans : ∀ {x y z} → x < y → y ≤ z → x < z
  <-≤-trans p q with ≤-strengthen q
  ... | inl y=z = subst₂ _<_ refl y=z p
  ... | inr y<z = <-trans p y<z

  ≤-<-trans : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤-<-trans p q with ≤-strengthen p
  ... | inl x=y = subst₂ _<_ (sym x=y) refl q
  ... | inr x<z = <-trans x<z q

  <-from-≤ : ∀ {x y} → x ≤ y → x ≠ y → x < y
  <-from-≤ x≤y x≠y with ≤-strengthen x≤y
  ... | inl x=y = absurd (x≠y x=y)
  ... | inr x<y = x<y

  *ℚ-cancel-<l : ∀ {x y r} ⦃ _ : Positive r ⦄ → (r *ℚ x) < (r *ℚ y) → x < y
  unquoteDef *ℚ-cancel-<l = do
    by-elim-ℚ *ℚ-cancel-<l λ d x y r ⦃ rpos ⦄ α →
      let instance _ = rpos .lower in
      common-denom-< (ℤ.*ℤ-cancel-<l {x = r} (<-common-denom ⦃ _ ⦄ α))

absℚ : Ratio → Ratio
absℚ (inc x) = Ratio.inc $ ℚ-rec absᶠ absᶠ-resp (inc x) where
  absᶠ : Fraction → _
  absᶠ (x / s [ p ]) = inc (pos (abs x) / s [ p ])

  absᶠ-resp : ∀ x y → x ≈ y → absᶠ x ≡ absᶠ y
  absᶠ-resp (pos x / possuc s [ p ]) (pos y / possuc t [ q ]) α = quot α
  absᶠ-resp (pos x / possuc s [ p ]) (negsuc y / possuc t [ q ]) α = absurd (pos≠negsuc (sym (ℤ.assign-pos (x * suc t)) ∙ from-same-rational α))
  absᶠ-resp (negsuc x / possuc s [ p ]) (pos y / possuc t [ q ]) α = absurd (negsuc≠pos (from-same-rational α ∙ ℤ.assign-pos (y * suc s)))
  absᶠ-resp (negsuc x / possuc s [ p ]) (negsuc y / possuc t [ q ]) α = quot (to-same-rational (ap possuc (negsuc-injective (from-same-rational α))))

≤-is-weakly-total : ∀ x y → ¬ (x ≤ y) → y ≤ x
≤-is-weakly-total = elim! λ where
  f@record{} f'@record{} ¬α → inc (ℤ.≤-is-weakly-total _ _ λ α → ¬α (inc α))
```
