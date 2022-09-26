```agda
open import 1Lab.Prelude

open import Data.Int

import Data.Nat as Nat

module Data.Int.Order where
```

# Ordering integers

```agda
private
  le-lemma
    : ∀ a b x y
    → I → n-Type lzero 1
  le-lemma a b x y i = n-ua
    {X = el (a + y Nat.≤ b + x) (Nat.≤-prop (a + y) (b + x))}
    {Y = el (a + suc y Nat.≤ b + suc x) (Nat.≤-prop (a + suc y) (b + suc x))}
    (prop-ext (Nat.≤-prop (a + y) _) (Nat.≤-prop (a + suc y) _)
      (λ p → transport (ap₂ Nat._≤_ (sym (Nat.+-sucr a y)) (sym (Nat.+-sucr b x))) p)
      (λ p → transport (ap₂ Nat._≤_ (Nat.+-sucr a y) (Nat.+-sucr b x)) p)) i

Int-le-prop : Int → Int → Prop lzero
Int-le-prop (diff a b) (diff c d)     = el _ (Nat.≤-prop (a + d) (b + c))
Int-le-prop (diff a b) (quot x y i)   = le-lemma a b x y i
Int-le-prop (quot m n i) (diff x y)   = el _ (Nat.≤-prop (m + y) (n + x))
Int-le-prop (quot a b i) (quot c d j) =
  n-Type-is-hlevel 1
    (el (a + d Nat.≤ b + c) (Nat.≤-prop (a + d) (b + c)))
    (el (a + suc d Nat.≤ b + suc c) (Nat.≤-prop (a + suc d) (b + suc c)))
    (λ i → le-lemma a b c d i)
    (λ i → le-lemma a b c d i) i j

_≤_ : Int → Int → Type
x ≤ y = ∣ Int-le-prop x y ∣

≤-refl : ∀ {x} → x ≤ x
≤-refl {x} = Int-elim-prop {P = λ x → x ≤ x} (λ _ → hlevel!)
  (λ a b → subst (λ e → a + b Nat.≤ e) (Nat.+-commutative a b) (Nat.≤-refl (a + b)))
  x

private
  sum≤0-l : ∀ x y → x + y Nat.≤ 0 → x ≡ 0
  sum≤0-l zero zero p = refl

  sum≤0-r : ∀ x y → x + y Nat.≤ 0 → y ≡ 0
  sum≤0-r zero zero p = refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {x} {y} {z} p q with by-sign x | by-sign y | by-sign z
... | negv x | posv y | posv z = tt
... | negv x | negv y | posv z = tt
... | posv x | posv y | posv z = Nat.≤-trans (x + 0) y z p (subst (Nat._≤ z) (Nat.+-zeror y) q)
... | negv x | negv y | negv z = Nat.≤-trans z (y + 0) (x + 0) q (subst (Nat._≤ x + 0) (sym (Nat.+-zeror y)) p)
... | posv x | posv y | negv z = absurd (Nat.zero≠suc (sym (sum≤0-r y (suc z) q)))
... | posv x | negv y | posv z = absurd (Nat.zero≠suc (sym (sum≤0-r x (suc y) p)))
... | posv x | negv y | negv z = absurd (Nat.zero≠suc (sym (sum≤0-r x (suc y) p)))
... | negv x | posv y | negv z = absurd (Nat.zero≠suc (sym (sum≤0-r y (suc z) q)))

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym {x} {y} p q with by-sign x | by-sign y
... | posv x | negv y = absurd (Nat.zero≠suc (sym (sum≤0-r x (suc y) p)))
... | negv x | posv y = absurd (Nat.zero≠suc (sym (sum≤0-r y (suc x) q)))
... | negv x | negv y = ap (λ e → diff 0 (suc e)) $
  Nat.≤-antisym x y
    (subst (x Nat.≤_) (Nat.+-zeror y) q)
    (subst (y Nat.≤_) (Nat.+-zeror x) p)
... | posv x | posv y = ap (λ e → diff e 0) $
  Nat.≤-antisym x y
    (subst (Nat._≤ y) (Nat.+-zeror x) p)
    (subst (Nat._≤ x) (Nat.+-zeror y) q)
```
