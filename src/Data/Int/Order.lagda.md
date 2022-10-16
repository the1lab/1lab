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
    → Path (n-Type lzero 1)
      (el (a + y Nat.≤ b + x) Nat.≤-prop)
      (el (a + suc y Nat.≤ b + suc x) Nat.≤-prop)
  le-lemma a b x y = n-ua
    (prop-ext Nat.≤-prop Nat.≤-prop
      (λ p → transport (ap₂ Nat._≤_ (sym (Nat.+-sucr a y)) (sym (Nat.+-sucr b x))) (Nat.s≤s p))
      (λ p → Nat.≤-peel (transport (ap₂ Nat._≤_ (Nat.+-sucr a y) (Nat.+-sucr b x)) p)))

  le-lemma′
    : ∀ a b x y
    → Path (n-Type lzero 1)
      (el (a + x Nat.≤ b + y) Nat.≤-prop)
      (el (suc (a + x) Nat.≤ suc (b + y)) Nat.≤-prop)
  le-lemma′ a b x y = n-ua
    (prop-ext Nat.≤-prop Nat.≤-prop Nat.s≤s λ { (Nat.s≤s x) → x })

Int-le-prop : Int → Int → Prop lzero
Int-le-prop (diff a b) (diff c d)     = el (a + d Nat.≤ b + c) Nat.≤-prop
Int-le-prop (diff a b) (quot x y i)   = le-lemma a b x y i
Int-le-prop (quot m n i) (diff x y)   = le-lemma′ m n y x i
Int-le-prop (quot a b i) (quot c d j) =
  is-set→squarep (λ _ _ → n-Type-is-hlevel 1)
    (λ i → le-lemma′ a b d c i)
    (λ i → le-lemma a b c d i)
    (n-ua
      (prop-ext Nat.≤-prop Nat.≤-prop
      (λ p →
          transport
          (ap₂ Nat._≤_ (sym (ap suc (Nat.+-sucr a d)))
          (sym (ap suc (Nat.+-sucr b c))))
          (Nat.s≤s p))
      (λ p →
          Nat.≤-peel
          (transport
          (ap₂ Nat._≤_ (ap suc (Nat.+-sucr a d)) (ap suc (Nat.+-sucr b c)))
          p))))
    (λ i → le-lemma′ a b (suc d) (suc c) i)
    i j

_≤_ : Int → Int → Type
x ≤ y = ∣ Int-le-prop x y ∣

≤-refl : ∀ {x} → x ≤ x
≤-refl {x} = Int-elim-prop {P = λ x → x ≤ x} (λ _ → hlevel!)
  (λ a b → subst (a + b Nat.≤_) (Nat.+-commutative a b) Nat.≤-refl)
  x

private
  sum≤0-l : ∀ x y → (x + y) Nat.≤ 0 → x ≡ 0
  sum≤0-l zero zero p = refl

  sum≤0-r : ∀ x y → (x + y) Nat.≤ 0 → y ≡ 0
  sum≤0-r zero zero p = refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans {x} {y} {z} p q with by-sign x | by-sign y | by-sign z
... | negv x | posv y | posv z = Nat.0≤x
... | negv x | negv y | posv z = Nat.0≤x
... | posv x | posv y | posv z = Nat.≤-trans p (subst (Nat._≤ z) (Nat.+-zeror y) q)
... | negv x | negv y | negv z = Nat.≤-trans q (subst (λ e → suc e Nat.≤ suc (x + 0)) (sym (Nat.+-zeror y)) p)
... | posv x | posv y | negv z = absurd (Nat.zero≠suc (sym (sum≤0-r y (suc z) q)))
... | posv x | negv y | posv z = absurd (Nat.zero≠suc (sym (sum≤0-r x (suc y) p)))
... | posv x | negv y | negv z = absurd (Nat.zero≠suc (sym (sum≤0-r x (suc y) p)))
... | negv x | posv y | negv z = absurd (Nat.zero≠suc (sym (sum≤0-r y (suc z) q)))

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym {x} {y} p q with by-sign x | by-sign y
... | posv x | negv y = absurd (Nat.zero≠suc (sym (sum≤0-r x (suc y) p)))
... | negv x | posv y = absurd (Nat.zero≠suc (sym (sum≤0-r y (suc x) q)))
... | negv x | negv y = ap (λ e → diff 0 (suc e)) $
  Nat.≤-antisym
    (subst (x Nat.≤_) (Nat.+-zeror y) (Nat.≤-peel q))
    (subst (y Nat.≤_) (Nat.+-zeror x) (Nat.≤-peel p))
... | posv x | posv y = ap (λ e → diff e 0) $
  Nat.≤-antisym
    (subst (Nat._≤ y) (Nat.+-zeror x) p)
    (subst (Nat._≤ x) (Nat.+-zeror y) q)
```
