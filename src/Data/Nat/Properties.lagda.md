```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Nat.Base

open import Relation.Order

module Data.Nat.Properties where
```

# Natural Numbers - Properties

This module contains proofs of arithmetic identities for [the natural
numbers]. Since they're mostly simple inductive arguments written in
[equational reasoning] style, they are very lightly commented:

[the natural numbers]: Data.Nat.Base.html
[equational reasoning]: 1Lab.Path.html#equational-reasoning

## Addition

```agda
+-associative : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+-associative zero y z = refl
+-associative (suc x) y z =
  suc ((x + y) + z) ≡⟨ ap suc (+-associative x y z) ⟩
  suc (x + (y + z)) ∎

+-zeror : (x : Nat) → x + 0 ≡ x
+-zeror zero = refl
+-zeror (suc x) =
  suc (x + 0) ≡⟨ ap suc (+-zeror x) ⟩
  suc x       ∎

+-sucr : (x y : Nat) → x + suc y ≡ suc (x + y)
+-sucr zero y = refl
+-sucr (suc x) y = ap suc (+-sucr x y)

+-commutative : (x y : Nat) → x + y ≡ y + x
+-commutative zero y = sym (+-zeror y)
+-commutative (suc x) y =
  suc (x + y) ≡⟨ ap suc (+-commutative x y) ⟩
  suc (y + x) ≡⟨ sym (+-sucr y x) ⟩
  y + suc x   ∎
```

## Multiplication

```agda
*-distrib-+r : (x y z : Nat) → (x + y) * z ≡ x * z + y * z
*-distrib-+r zero y z = refl
*-distrib-+r (suc x) y z =
  z + (x + y) * z     ≡⟨ ap₂ _+_ refl (*-distrib-+r x y z) ⟩
  z + (x * z + y * z) ≡⟨ sym (+-associative z (x * z) (y * z)) ⟩
  z + x * z + y * z   ∎

*-sucr : (m n : Nat) → m * suc n ≡ m + m * n
*-sucr zero    n = refl
*-sucr (suc m) n =
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ ap₂ _+_ refl (*-sucr m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ ap suc (sym (+-associative n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ ap (λ x → suc (x + m * n)) (+-commutative n m) ⟩
  suc (m + n + m * n)   ≡⟨ ap suc (+-associative m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

*-onel : (x : Nat) → 1 * x ≡ x
*-onel x = +-zeror x

*-oner : (x : Nat) → x * 1 ≡ x
*-oner zero = refl
*-oner (suc x) =
  suc (x * 1) ≡⟨ ap suc (*-oner x) ⟩
  suc x       ∎

*-zeror : (x : Nat) → x * 0 ≡ 0
*-zeror zero = refl
*-zeror (suc x) = *-zeror x

*-commutative : (x y : Nat) → x * y ≡ y * x
*-commutative zero y    = sym (*-zeror y)
*-commutative (suc x) y =
  y + x * y ≡⟨ ap₂ _+_ refl (*-commutative x y) ⟩
  y + y * x ≡⟨ sym (*-sucr y x) ⟩
  y * suc x ∎

*-distrib-+l : (x y z : Nat) → z * (x + y) ≡ z * x + z * y
*-distrib-+l x y z =
  z * (x + y)   ≡⟨ *-commutative z (x + y) ⟩
  (x + y) * z   ≡⟨ *-distrib-+r x y z ⟩
  x * z + y * z ≡⟨ ap₂ _+_ (*-commutative x z) (*-commutative y z) ⟩
  z * x + z * y ∎

*-associative : (x y z : Nat) → (x * y) * z ≡ x * (y * z)
*-associative zero y z = refl
*-associative (suc x) y z =
  (y + x * y) * z     ≡⟨ *-distrib-+r y (x * y) z ⟩
  y * z + (x * y) * z ≡⟨ ap₂ _+_ refl (*-associative x y z) ⟩
  y * z + x * (y * z) ∎
```

## Exponentiation

```agda
^-oner : (x : Nat) → x ^ 1 ≡ x
^-oner x = *-oner x

^-onel : (x : Nat) → 1 ^ x ≡ 1
^-onel zero = refl
^-onel (suc x) =
  (1 ^ x) + 0 ≡⟨ +-zeror (1 ^ x) ⟩
  (1 ^ x)     ≡⟨ ^-onel x ⟩
  1 ∎

^-+-hom-*r : (x y z : Nat) → x ^ (y + z) ≡ (x ^ y) * (x ^ z)
^-+-hom-*r x zero z = sym (+-zeror (x ^ z))
^-+-hom-*r x (suc y) z =
  x * x ^ (y + z)     ≡⟨ ap (x *_) (^-+-hom-*r x y z) ⟩
  x * (x ^ y * x ^ z) ≡⟨ sym (*-associative x (x ^ y) (x ^ z)) ⟩
  x * x ^ y * x ^ z ∎

^-distrib-*r : (x y z : Nat) → (x * y) ^ z ≡ x ^ z * y ^ z
^-distrib-*r x y zero = refl
^-distrib-*r x y (suc z) =
  x * y * (x * y) ^ z     ≡⟨ ap (λ a → x * y * a) (^-distrib-*r x y z) ⟩
  x * y * (x ^ z * y ^ z) ≡⟨ sym (*-associative (x * y) (x ^ z) (y ^ z)) ⟩
  x * y * x ^ z * y ^ z   ≡⟨ ap (_* y ^ z) (*-associative x y (x ^ z)) ⟩
  x * (y * x ^ z) * y ^ z ≡⟨ ap (λ a → x * a * y ^ z) (*-commutative y (x ^ z)) ⟩
  x * (x ^ z * y) * y ^ z ≡⟨ ap (_* y ^ z) (sym (*-associative x (x ^ z) y)) ⟩
  x * x ^ z * y * y ^ z   ≡⟨ *-associative (x * x ^ z) y (y ^ z) ⟩
  x * x ^ z * (y * y ^ z) ∎

^-*-adjunct : (x y z : Nat) → (x ^ y) ^ z ≡ x ^ (y * z)
^-*-adjunct x zero z = ^-onel z
^-*-adjunct x (suc y) zero = ^-*-adjunct x y zero
^-*-adjunct x (suc y) (suc z) =
  x * x ^ y * (x * x ^ y) ^ z       ≡⟨ ap (λ a → x * x ^ y * a) (^-distrib-*r x (x ^ y) z) ⟩
  x * x ^ y * (x ^ z * (x ^ y) ^ z) ≡⟨ ap (λ a → x * x ^ y * (x ^ z * a)) (^-*-adjunct x y z) ⟩
  x * x ^ y * (x ^ z * x ^ (y * z)) ≡⟨ ap (λ a → x * x ^ y * a) (sym (^-+-hom-*r x z (y * z))) ⟩
  x * x ^ y * (x ^ (z + (y * z)))   ≡⟨ *-associative x (x ^ y) (x ^ (z + y * z)) ⟩
  x * (x ^ y * (x ^ (z + (y * z)))) ≡⟨ ap (x *_) (sym (^-+-hom-*r x y (z + y * z))) ⟩
  x * x ^ (y + (z + y * z))         ≡⟨ ap (λ a → x * x ^ a) (sym (+-associative y z (y * z))) ⟩
  x * x ^ (y + z + y * z)           ≡⟨ ap (λ a → x * x ^ (a + y * z)) (+-commutative y z) ⟩
  x * x ^ (z + y + y * z)           ≡⟨ ap (λ a → x * x ^ a) (+-associative z y (y * z)) ⟩
  x * x ^ (z + (y + y * z))         ≡⟨ ap (λ a → x * x ^ (z + a)) (sym (*-sucr y z))  ⟩
  x * x ^ (z + y * suc z) ∎
```

## Ordering

The ordering relation on the natural numbers is a partial order:

```agda
≤-is-preorder : is-preorder _≤_
≤-is-preorder .is-preorder.reflexive {x} = ≤-refl x
≤-is-preorder .is-preorder.transitive {x} {y} {z} = ≤-trans x y z
≤-is-preorder .is-preorder.propositional {x} {y} = ≤-prop x y

≤-is-partial-order : is-partial-order _≤_
≤-is-partial-order .is-partial-order.preorder = ≤-is-preorder
≤-is-partial-order .is-partial-order.antisym {x} {y} = ≤-antisym x y
```

We also have that a successor is never smaller than the number it
succeeds:

```agda
¬sucx≤x : (x : Nat) → suc x ≤ x → ⊥
¬sucx≤x (suc x) ord = ¬sucx≤x x ord
```

### Compatibility

The order relation on the natural numbers is also compatible with the
arithmetic operators:

```agda
+-preserves-≤l : (x y z : Nat) → x ≤ y → z + x ≤ z + y
+-preserves-≤l x y zero prf = prf
+-preserves-≤l x y (suc z) prf = +-preserves-≤l x y z prf

+-preserves-≤r : (x y z : Nat) → x ≤ y → x + z ≤ y + z
+-preserves-≤r x y z prf = subst (λ a → a ≤ y + z) (+-commutative z x)
  (subst (λ a → z + x ≤ a) (+-commutative z y) (+-preserves-≤l x y z prf))

+-preserves-≤ : (x y x' y' : Nat) → x ≤ y → x' ≤ y' → x + x' ≤ y + y'
+-preserves-≤ x y x' y' prf prf' = ≤-trans (x + x') (y + x') (y + y')
  (+-preserves-≤r x y x' prf) (+-preserves-≤l x' y' y prf')

*-preserves-≤l : (x y z : Nat) → x ≤ y → z * x ≤ z * y
*-preserves-≤l x y zero prf = tt
*-preserves-≤l x y (suc z) prf = +-preserves-≤ x y (z * x) (z * y) prf
  (*-preserves-≤l x y z prf)

*-preserves-≤r : (x y z : Nat) → x ≤ y → x * z ≤ y * z
*-preserves-≤r x y z prf = subst (λ a → a ≤ y * z) (*-commutative z x)
  (subst (λ a → z * x ≤ a) (*-commutative z y) (*-preserves-≤l x y z prf))

*-preserves-≤ : (x y x' y' : Nat) → x ≤ y → x' ≤ y' → x * x' ≤ y * y'
*-preserves-≤ x y x' y' prf prf' = ≤-trans (x * x') (y * x') (y * y')
  (*-preserves-≤r x y x' prf) (*-preserves-≤l x' y' y prf')

+-reflects-≤l : (x y z : Nat) → z + x ≤ z + y → x ≤ y
+-reflects-≤l x y zero prf = prf
+-reflects-≤l x y (suc z) prf = +-reflects-≤l x y z prf

+-reflects-≤r : (x y z : Nat) → x + z ≤ y + z → x ≤ y
+-reflects-≤r x y z prf =
  +-reflects-≤l x y z
    (subst (_≤ z + y) (+-commutative x z)
    (subst (x + z ≤_) (+-commutative y z) prf))
```

### Maximum

```agda
max-assoc : (x y z : Nat) → max x (max y z) ≡ max (max x y) z
max-assoc zero zero zero = refl
max-assoc zero zero (suc z) = refl
max-assoc zero (suc y) zero = refl
max-assoc zero (suc y) (suc z) = refl
max-assoc (suc x) zero zero = refl
max-assoc (suc x) zero (suc z) = refl
max-assoc (suc x) (suc y) zero = refl
max-assoc (suc x) (suc y) (suc z) = ap suc (max-assoc x y z)

max-≤l : (x y : Nat) → x ≤ max x y
max-≤l zero zero = tt
max-≤l zero (suc y) = tt
max-≤l (suc x) zero = ≤-refl (suc x)
max-≤l (suc x) (suc y) = max-≤l x y

max-≤r : (x y : Nat) → y ≤ max x y
max-≤r zero zero = tt
max-≤r zero (suc y) = ≤-refl (suc y)
max-≤r (suc x) zero = tt
max-≤r (suc x) (suc y) = max-≤r x y
```

### Minimum

```agda
min-assoc : (x y z : Nat) → min x (min y z) ≡ min (min x y) z
min-assoc zero zero zero = refl
min-assoc zero zero (suc z) = refl
min-assoc zero (suc y) zero = refl
min-assoc zero (suc y) (suc z) = refl
min-assoc (suc x) zero zero = refl
min-assoc (suc x) zero (suc z) = refl
min-assoc (suc x) (suc y) zero = refl
min-assoc (suc x) (suc y) (suc z) = ap suc (min-assoc x y z)

min-≤l : (x y : Nat) → min x y ≤ x
min-≤l zero zero = tt
min-≤l zero (suc y) = tt
min-≤l (suc x) zero = tt
min-≤l (suc x) (suc y) = min-≤l x y

min-≤r : (x y : Nat) → min x y ≤ y
min-≤r zero zero = tt
min-≤r zero (suc y) = tt
min-≤r (suc x) zero = tt
min-≤r (suc x) (suc y) = min-≤r x y
```
