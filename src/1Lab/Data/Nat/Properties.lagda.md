```agda
open import 1Lab.Data.Relation.Order
open import 1Lab.Data.Nat.Base
open import 1Lab.HLevel.Sets
open import 1Lab.Data.Dec
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Data.Nat.Properties where
```

# Natural Numbers - Properties

This module contains proofs of arithmetic identities for [the natural
numbers]. Since they're mostly simple inductive arguments written in
[equational reasoning] style, they are very lightly commented:

[the natural numbers]: 1Lab.Data.Nat.Base.html
[equational reasoning]: 1Lab.Path.html#equational-reasoning

## Addition

```agda
+-associative : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+-associative zero y z = refl
+-associative (suc x) y z =
  suc ((x + y) + z) ≡⟨ ap suc (+-associative x y z) ⟩
  suc (x + (y + z)) ∎

+-zeroʳ : (x : Nat) → x + 0 ≡ x
+-zeroʳ zero = refl
+-zeroʳ (suc x) =
  suc (x + 0) ≡⟨ ap suc (+-zeroʳ x) ⟩
  suc x       ∎

+-sucʳ : (x y : Nat) → x + suc y ≡ suc (x + y)
+-sucʳ zero y = refl
+-sucʳ (suc x) y = ap suc (+-sucʳ x y)

+-commutative : (x y : Nat) → x + y ≡ y + x
+-commutative zero y = sym (+-zeroʳ y)
+-commutative (suc x) y =
  suc (x + y) ≡⟨ ap suc (+-commutative x y) ⟩
  suc (y + x) ≡⟨ sym (+-sucʳ y x) ⟩
  y + suc x   ∎
```

## Multiplication

```agda
*-distrib-+ʳ : (x y z : Nat) → (x + y) * z ≡ x * z + y * z
*-distrib-+ʳ zero y z = refl
*-distrib-+ʳ (suc x) y z =
  z + (x + y) * z     ≡⟨ ap₂ _+_ refl (*-distrib-+ʳ x y z) ⟩
  z + (x * z + y * z) ≡⟨ sym (+-associative z (x * z) (y * z)) ⟩
  z + x * z + y * z   ∎

*-sucʳ : (m n : Nat) → m * suc n ≡ m + m * n
*-sucʳ zero    n = refl
*-sucʳ (suc m) n =
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ ap₂ _+_ refl (*-sucʳ m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ ap suc (sym (+-associative n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ ap (λ x → suc (x + m * n)) (+-commutative n m) ⟩
  suc (m + n + m * n)   ≡⟨ ap suc (+-associative m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

*-oneʳ : (x : Nat) → x * 1 ≡ x
*-oneʳ zero = refl
*-oneʳ (suc x) =
  suc (x * 1) ≡⟨ ap suc (*-oneʳ x) ⟩
  suc x       ∎

*-zeroʳ : (x : Nat) → x * 0 ≡ 0
*-zeroʳ zero = refl
*-zeroʳ (suc x) = *-zeroʳ x

*-commutative : (x y : Nat) → x * y ≡ y * x
*-commutative zero y    = sym (*-zeroʳ y)
*-commutative (suc x) y =
  y + x * y ≡⟨ ap₂ _+_ refl (*-commutative x y) ⟩
  y + y * x ≡⟨ sym (*-sucʳ y x) ⟩
  y * suc x ∎

*-distrib-+ˡ : (x y z : Nat) → z * (x + y) ≡ z * x + z * y
*-distrib-+ˡ x y z =
  z * (x + y)   ≡⟨ *-commutative z (x + y) ⟩
  (x + y) * z   ≡⟨ *-distrib-+ʳ x y z ⟩
  x * z + y * z ≡⟨ ap₂ _+_ (*-commutative x z) (*-commutative y z) ⟩
  z * x + z * y ∎

*-associative : (x y z : Nat) → (x * y) * z ≡ x * (y * z)
*-associative zero y z = refl
*-associative (suc x) y z =
  (y + x * y) * z     ≡⟨ *-distrib-+ʳ y (x * y) z ⟩
  y * z + (x * y) * z ≡⟨ ap₂ _+_ refl (*-associative x y z) ⟩
  y * z + x * (y * z) ∎
```

## Exponentiation

```agda
^-oneʳ : (x : Nat) → x ^ 1 ≡ x
^-oneʳ x = *-oneʳ x

^-oneˡ : (x : Nat) → 1 ^ x ≡ 1
^-oneˡ zero = refl
^-oneˡ (suc x) =
  (1 ^ x) + 0 ≡⟨ +-zeroʳ (1 ^ x) ⟩
  (1 ^ x)     ≡⟨ ^-oneˡ x ⟩
  1 ∎

^-+-hom-*ʳ : (x y z : Nat) → x ^ (y + z) ≡ (x ^ y) * (x ^ z)
^-+-hom-*ʳ x zero z = sym (+-zeroʳ (x ^ z))
^-+-hom-*ʳ x (suc y) z =
  x * x ^ (y + z)     ≡⟨ ap (x *_) (^-+-hom-*ʳ x y z) ⟩
  x * (x ^ y * x ^ z) ≡⟨ sym (*-associative x (x ^ y) (x ^ z)) ⟩
  x * x ^ y * x ^ z ∎

^-distrib-*ʳ : (x y z : Nat) → (x * y) ^ z ≡ x ^ z * y ^ z
^-distrib-*ʳ x y zero = refl
^-distrib-*ʳ x y (suc z) =
  x * y * (x * y) ^ z     ≡⟨ ap (λ a → x * y * a) (^-distrib-*ʳ x y z) ⟩
  x * y * (x ^ z * y ^ z) ≡⟨ sym (*-associative (x * y) (x ^ z) (y ^ z)) ⟩
  x * y * x ^ z * y ^ z   ≡⟨ ap (_* y ^ z) (*-associative x y (x ^ z)) ⟩
  x * (y * x ^ z) * y ^ z ≡⟨ ap (λ a → x * a * y ^ z) (*-commutative y (x ^ z)) ⟩
  x * (x ^ z * y) * y ^ z ≡⟨ ap (_* y ^ z) (sym (*-associative x (x ^ z) y)) ⟩
  x * x ^ z * y * y ^ z   ≡⟨ *-associative (x * x ^ z) y (y ^ z) ⟩
  x * x ^ z * (y * y ^ z) ∎

^-*-adjunct : (x y z : Nat) → (x ^ y) ^ z ≡ x ^ (y * z)
^-*-adjunct x zero z = ^-oneˡ z
^-*-adjunct x (suc y) zero = ^-*-adjunct x y zero
^-*-adjunct x (suc y) (suc z) =
  x * x ^ y * (x * x ^ y) ^ z       ≡⟨ ap (λ a → x * x ^ y * a) (^-distrib-*ʳ x (x ^ y) z) ⟩
  x * x ^ y * (x ^ z * (x ^ y) ^ z) ≡⟨ ap (λ a → x * x ^ y * (x ^ z * a)) (^-*-adjunct x y z) ⟩
  x * x ^ y * (x ^ z * x ^ (y * z)) ≡⟨ ap (λ a → x * x ^ y * a) (sym (^-+-hom-*ʳ x z (y * z))) ⟩
  x * x ^ y * (x ^ (z + (y * z)))   ≡⟨ *-associative x (x ^ y) (x ^ (z + y * z)) ⟩
  x * (x ^ y * (x ^ (z + (y * z)))) ≡⟨ ap (x *_) (sym (^-+-hom-*ʳ x y (z + y * z))) ⟩
  x * x ^ (y + (z + y * z))         ≡⟨ ap (λ a → x * x ^ a) (sym (+-associative y z (y * z))) ⟩
  x * x ^ (y + z + y * z)           ≡⟨ ap (λ a → x * x ^ (a + y * z)) (+-commutative y z) ⟩
  x * x ^ (z + y + y * z)           ≡⟨ ap (λ a → x * x ^ a) (+-associative z y (y * z)) ⟩
  x * x ^ (z + (y + y * z))         ≡⟨ ap (λ a → x * x ^ (z + a)) (sym (*-sucʳ y z))  ⟩
  x * x ^ (z + y * suc z) ∎
```

## Ordering

The ordering relation on the natural numbers is a partial order:

```agda
≤-Preorder : isPreorder _≤_
≤-Preorder .isPreorder.reflexive {x} = ≤-refl x
≤-Preorder .isPreorder.transitive {x} {y} {z} = ≤-trans x y z
≤-Preorder .isPreorder.propositional {x} {y} = ≤-prop x y

≤-PartialOrder : isPartialOrder _≤_
≤-PartialOrder .isPartialOrder.preorder = ≤-Preorder
≤-PartialOrder .isPartialOrder.antisym {x} {y} = ≤-antisym x y
```

### Compatibility

The order relation on the natural numbers is also compatible with the
arithmetic operators:

```agda
+-preserves-≤ˡ : (x y z : Nat) → x ≤ y → z + x ≤ z + y
+-preserves-≤ˡ x y zero prf = prf
+-preserves-≤ˡ x y (suc z) prf = +-preserves-≤ˡ x y z prf

+-preserves-≤ʳ : (x y z : Nat) → x ≤ y → x + z ≤ y + z
+-preserves-≤ʳ x y z prf = subst (λ a → a ≤ y + z) (+-commutative z x)
  (subst (λ a → z + x ≤ a) (+-commutative z y) (+-preserves-≤ˡ x y z prf))

+-preserves-≤ : (x y x' y' : Nat) → x ≤ y → x' ≤ y' → x + x' ≤ y + y'
+-preserves-≤ x y x' y' prf prf' = ≤-trans (x + x') (y + x') (y + y')
  (+-preserves-≤ʳ x y x' prf) (+-preserves-≤ˡ x' y' y prf')

*-preserves-≤ˡ : (x y z : Nat) → x ≤ y → z * x ≤ z * y
*-preserves-≤ˡ x y zero prf = tt
*-preserves-≤ˡ x y (suc z) prf = +-preserves-≤ x y (z * x) (z * y) prf
  (*-preserves-≤ˡ x y z prf)

*-preserves-≤ʳ : (x y z : Nat) → x ≤ y → x * z ≤ y * z
*-preserves-≤ʳ x y z prf = subst (λ a → a ≤ y * z) (*-commutative z x)
  (subst (λ a → z * x ≤ a) (*-commutative z y) (*-preserves-≤ˡ x y z prf))

*-preserves-≤ : (x y x' y' : Nat) → x ≤ y → x' ≤ y' → x * x' ≤ y * y'
*-preserves-≤ x y x' y' prf prf' = ≤-trans (x * x') (y * x') (y * y')
  (*-preserves-≤ʳ x y x' prf) (*-preserves-≤ˡ x' y' y prf')

+-reflects-≤ˡ : (x y z : Nat) → z + x ≤ z + y → x ≤ y
+-reflects-≤ˡ x y zero prf = prf
+-reflects-≤ˡ x y (suc z) prf = +-reflects-≤ˡ x y z prf

+-reflects-≤ʳ : (x y z : Nat) → x + z ≤ y + z → x ≤ y
+-reflects-≤ʳ x y z prf =
  +-reflects-≤ˡ x y z
    (subst (_≤ z + y) (+-commutative x z)
    (subst (x + z ≤_) (+-commutative y z) prf))
```
