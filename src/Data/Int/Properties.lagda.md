<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Int.Base
open import Data.Nat.Base
```
-->

```agda
module Data.Int.Properties where
```

<!--
```agda
abstract
```
-->

# Properties of integers

This module establishes arithmetic and algebraic properties of the
integers. Most of the proofs are straightforward case bashes; there are
no further comments.

## Differences

```agda
  nat-diff-zero : ∀ x → (x ℕ- x) ≡ 0
  nat-diff-zero zero    = refl
  nat-diff-zero (suc x) = nat-diff-zero x

  sucℤ-nat-diff : ∀ x y → sucℤ (x ℕ- y) ≡ suc x ℕ- y
  sucℤ-nat-diff zero zero          = refl
  sucℤ-nat-diff zero (suc zero)    = refl
  sucℤ-nat-diff zero (suc (suc y)) = refl
  sucℤ-nat-diff (suc x) zero       = refl
  sucℤ-nat-diff (suc x) (suc y)    = sucℤ-nat-diff x y

  predℤ-nat-diff : ∀ x y → predℤ (x ℕ- y) ≡ x ℕ- suc y
  predℤ-nat-diff zero zero       = refl
  predℤ-nat-diff zero (suc y)    = refl
  predℤ-nat-diff (suc x) zero    = refl
  predℤ-nat-diff (suc x) (suc y) = predℤ-nat-diff x y
```

## Negations

```agda
  negℤ-negℤ : ∀ x → negℤ (negℤ x) ≡ x
  negℤ-negℤ (pos zero)    = refl
  negℤ-negℤ (pos (suc x)) = refl
  negℤ-negℤ (negsuc x)    = refl

  negℤ-injective : ∀ x y → negℤ x ≡ negℤ y → x ≡ y
  negℤ-injective x y p = sym (negℤ-negℤ x) ·· ap negℤ p ·· negℤ-negℤ y

  negℤ-predℤ : ∀ x → negℤ (predℤ x) ≡ sucℤ (negℤ x)
  negℤ-predℤ posz             = refl
  negℤ-predℤ (possuc zero)    = refl
  negℤ-predℤ (possuc (suc x)) = refl
  negℤ-predℤ (negsuc x)       = refl

  negℤ-sucℤ : ∀ x → negℤ (sucℤ x) ≡ predℤ (negℤ x)
  negℤ-sucℤ posz             = refl
  negℤ-sucℤ (possuc x)       = refl
  negℤ-sucℤ (negsuc zero)    = refl
  negℤ-sucℤ (negsuc (suc x)) = refl

  negℤ-distrib-max : ∀ x y → negℤ (maxℤ x y) ≡ minℤ (negℤ x) (negℤ y)
  negℤ-distrib-max posz       posz       = refl
  negℤ-distrib-max posz       (possuc y) = refl
  negℤ-distrib-max posz       (negsuc y) = refl
  negℤ-distrib-max (possuc x) posz       = refl
  negℤ-distrib-max (possuc x) (possuc y) = refl
  negℤ-distrib-max (possuc x) (negsuc y) = refl
  negℤ-distrib-max (negsuc x) posz       = refl
  negℤ-distrib-max (negsuc x) (possuc y) = refl
  negℤ-distrib-max (negsuc x) (negsuc y) = refl

  negℤ-distrib-min : ∀ x y → negℤ (minℤ x y) ≡ maxℤ (negℤ x) (negℤ y)
  negℤ-distrib-min posz       posz       = refl
  negℤ-distrib-min posz       (possuc y) = refl
  negℤ-distrib-min posz       (negsuc y) = refl
  negℤ-distrib-min (possuc x) posz       = refl
  negℤ-distrib-min (possuc x) (possuc y) = refl
  negℤ-distrib-min (possuc x) (negsuc y) = refl
  negℤ-distrib-min (negsuc x) posz       = refl
  negℤ-distrib-min (negsuc x) (possuc y) = refl
  negℤ-distrib-min (negsuc x) (negsuc y) = refl
```

## Rotations

```agda
  rot-pos : ∀ x y → rotℤ (pos x) (pos y) ≡ pos (x + y)
  rot-pos zero    y = refl
  rot-pos (suc x) y = ap sucℤ (rot-pos x y)

  rot-negsuc : ∀ x y → rotℤ (negsuc x) (negsuc y) ≡ negsuc (suc (x + y))
  rot-negsuc zero    y = refl
  rot-negsuc (suc x) y = ap predℤ (rot-negsuc x y)

  rot-pos-neg : ∀ x y → sucℤ (rotℤ (pos x) (negsuc y)) ≡ x ℕ- y
  rot-pos-neg zero zero    = refl
  rot-pos-neg zero (suc y) = refl
  rot-pos-neg (suc x) y    = ap sucℤ (rot-pos-neg x y) ∙ sucℤ-nat-diff x y

  rot-neg-pos : ∀ x y → rotℤ (negsuc x) (pos y) ≡ y ℕ- suc x
  rot-neg-pos zero zero    = refl
  rot-neg-pos zero (suc y) = refl
  rot-neg-pos (suc x) y    = ap predℤ (rot-neg-pos x y) ∙ predℤ-nat-diff y (suc x)

  rot-sucl : ∀ x y → rotℤ (sucℤ x) y ≡ sucℤ (rotℤ x y)
  rot-sucl (pos x)          y = refl
  rot-sucl (negsuc zero)    y = sym (suc-predℤ y)
  rot-sucl (negsuc (suc x)) y = sym (suc-predℤ _)

  rot-predl : ∀ x y → rotℤ (predℤ x) y ≡ predℤ (rotℤ x y)
  rot-predl posz       y = refl
  rot-predl (possuc x) y = sym (pred-sucℤ _)
  rot-predl (negsuc x) y = refl

  negℤ-distrib-rot : ∀ x y → negℤ (rotℤ x y) ≡ rotℤ (negℤ x) (negℤ y)
  negℤ-distrib-rot posz             y = refl
  negℤ-distrib-rot (possuc zero)    y = negℤ-sucℤ y
  negℤ-distrib-rot (possuc (suc x)) y =
    negℤ-sucℤ (sucℤ (rotℤ (pos x) y)) ∙ ap predℤ (negℤ-distrib-rot (pos (suc x)) y)
  negℤ-distrib-rot (negsuc zero)    y = negℤ-predℤ y
  negℤ-distrib-rot (negsuc (suc x)) y =
      negℤ-predℤ (rotℤ (negsuc x) y)
    ∙ ap sucℤ (negℤ-distrib-rot (negsuc x) y)

  rotℤ-assoc : ∀ x y z → rotℤ x (rotℤ y z) ≡ rotℤ (rotℤ x y) z
  rotℤ-assoc (pos zero)    y z = refl
  rotℤ-assoc (pos (suc x)) y z =
    sucℤ (rotℤ (pos x) (rotℤ y z)) ≡⟨ ap sucℤ (rotℤ-assoc (pos x) y z) ⟩
    sucℤ (rotℤ (rotℤ (pos x) y) z) ≡˘⟨ rot-sucl (rotℤ (pos x) y) z ⟩
    rotℤ (sucℤ (rotℤ (pos x) y)) z  ∎
  rotℤ-assoc (negsuc zero) y z = sym (rot-predl y z)
  rotℤ-assoc (negsuc (suc x)) y z =
    predℤ (rotℤ (negsuc x) (rotℤ y z)) ≡⟨ ap predℤ (rotℤ-assoc (negsuc x) y z) ⟩
    predℤ (rotℤ (rotℤ (negsuc x) y) z) ≡˘⟨ rot-predl (rotℤ (negsuc x) y) z ⟩
    rotℤ (predℤ (rotℤ (negsuc x) y)) z ∎
```

## Addition

```agda
  +ℤ-zerol : ∀ x → 0 +ℤ x ≡ x
  +ℤ-zerol (pos x)    = refl
  +ℤ-zerol (negsuc x) = refl

  +ℤ-zeror : ∀ x → x +ℤ 0 ≡ x
  +ℤ-zeror (pos x)    = ap pos (+-zeror x)
  +ℤ-zeror (negsuc x) = refl

  rot-is-add : ∀ x y → x +ℤ y ≡ rotℤ x y
  rot-is-add (pos zero)    x          = +ℤ-zerol x
  rot-is-add (pos (suc x)) (pos y)    = sym (ap sucℤ (rot-pos x y))
  rot-is-add (pos (suc x)) (negsuc y) = sym (rot-pos-neg x y)
  rot-is-add (negsuc x) (pos y)       = sym (rot-neg-pos x y)
  rot-is-add (negsuc x) (negsuc y)    = sym (rot-negsuc x y)

  +ℤ-assoc : ∀ x y z → x +ℤ (y +ℤ z) ≡ (x +ℤ y) +ℤ z
  +ℤ-assoc x y z =
    x +ℤ (y +ℤ z)     ≡⟨ ap (x +ℤ_) (rot-is-add y z) ⟩
    x +ℤ rotℤ y z     ≡⟨ rot-is-add x _ ⟩
    rotℤ x (rotℤ y z) ≡⟨ rotℤ-assoc x y z ⟩
    rotℤ (rotℤ x y) z ≡˘⟨ ap₂ rotℤ (rot-is-add x y) refl ⟩
    rotℤ (x +ℤ y) z   ≡˘⟨ rot-is-add (x +ℤ y) z ⟩
    (x +ℤ y) +ℤ z     ∎

  +ℤ-invl : ∀ x → negℤ x +ℤ x ≡ 0
  +ℤ-invl (pos zero)    = refl
  +ℤ-invl (pos (suc x)) = nat-diff-zero x
  +ℤ-invl (negsuc x)    = nat-diff-zero x

  +ℤ-invr : ∀ x → x +ℤ negℤ x ≡ 0
  +ℤ-invr (pos zero)    = refl
  +ℤ-invr (pos (suc x)) = nat-diff-zero x
  +ℤ-invr (negsuc x)    = nat-diff-zero x

  +ℤ-commutative : ∀ x y → x +ℤ y ≡ y +ℤ x
  +ℤ-commutative (pos x)    (pos y)    = ap pos (+-commutative x y)
  +ℤ-commutative (pos x)    (negsuc y) = refl
  +ℤ-commutative (negsuc x) (pos y)    = refl
  +ℤ-commutative (negsuc x) (negsuc y) = ap negsuc (ap suc (+-commutative x y))

  +ℤ-sucl : ∀ x y → sucℤ x +ℤ y ≡ sucℤ (x +ℤ y)
  +ℤ-sucl x y = rot-is-add (sucℤ x) y ·· rot-sucl x y ·· ap sucℤ (sym (rot-is-add x y))

  +ℤ-sucr : ∀ x y → x +ℤ sucℤ y ≡ sucℤ (x +ℤ y)
  +ℤ-sucr x y = +ℤ-commutative x (sucℤ y) ·· +ℤ-sucl y x ·· ap sucℤ (+ℤ-commutative y x)

  +ℤ-predl : ∀ x y → predℤ x +ℤ y ≡ predℤ (x +ℤ y)
  +ℤ-predl x y = rot-is-add (predℤ x) y ·· rot-predl x y ·· ap predℤ (sym (rot-is-add x y))

  +ℤ-predr : ∀ x y → x +ℤ predℤ y ≡ predℤ (x +ℤ y)
  +ℤ-predr x y = +ℤ-commutative x (predℤ y) ·· +ℤ-predl y x ·· ap predℤ (+ℤ-commutative y x)

  +ℤ-injectiver : ∀ k x y → k +ℤ x ≡ k +ℤ y → x ≡ y
  +ℤ-injectiver k x y p =
      sym (+ℤ-zerol x)
    ·· ap (_+ℤ x) (sym (+ℤ-invl k))
    ·· sym (+ℤ-assoc (negℤ k) k x)
    ·· ap (negℤ k +ℤ_) p
    ·· +ℤ-assoc (negℤ k) k y
    ·· ap (_+ℤ y) (+ℤ-invl k)
    ·· +ℤ-zerol y

  +ℤ-injectivel : ∀ k x y → x +ℤ k ≡ y +ℤ k → x ≡ y
  +ℤ-injectivel k x y p = +ℤ-injectiver k x y $
    +ℤ-commutative k x ·· p ·· +ℤ-commutative y k

  negℤ-distrib : ∀ x y → negℤ (x +ℤ y) ≡ (negℤ x) +ℤ (negℤ y)
  negℤ-distrib x y =
      ap negℤ (rot-is-add x y)
    ·· negℤ-distrib-rot x y
    ·· sym (rot-is-add (negℤ x) (negℤ y))
```

## Multiplication

```agda
  assign-pos : ∀ x → assign pos x ≡ pos x
  assign-pos zero    = refl
  assign-pos (suc x) = refl

  *ℤ-onel : ∀ x → 1 *ℤ x ≡ x
  *ℤ-onel (pos x)    = ap (assign pos) (+-zeror x) ∙ assign-pos x
  *ℤ-onel (negsuc x) = ap negsuc (+-zeror x)

  *ℤ-oner : ∀ x → x *ℤ 1 ≡ x
  *ℤ-oner (pos x)    = ap (assign pos) (*-oner x) ∙ assign-pos x
  *ℤ-oner (negsuc x) = ap negsuc (*-oner x)

  *ℤ-zerol : ∀ x → 0 *ℤ x ≡ 0
  *ℤ-zerol (pos x)    = refl
  *ℤ-zerol (negsuc x) = refl

  *ℤ-zeror : ∀ x → x *ℤ 0 ≡ 0
  *ℤ-zeror (pos x)    = ap (assign pos) (*-zeror x)
  *ℤ-zeror (negsuc x) = ap (assign neg) (*-zeror x)

  private
    lemma : ∀ x y z → z + y * suc z + x * suc (z + y * suc z)  ≡ z + (y + x * suc y) * suc z
    lemma x y z = nat!

  *ℤ-associative : ∀ x y z → x *ℤ (y *ℤ z) ≡ (x *ℤ y) *ℤ z
  *ℤ-associative posz y z = refl
  *ℤ-associative x posz z =
    ap (λ e → assign (sign× (sign x) pos) e) (*-zeror (abs x)) ∙ sym (ap
      (λ e → assign
        (sign× (sign (assign (sign× (sign x) pos) e)) (sign z))
        (abs (assign (sign× (sign x) pos) e) * abs z)) (*-zeror (abs x)))
  *ℤ-associative x y posz =
    ap (λ e →
      assign (sign× (sign x) (sign (assign (sign× (sign y) pos) e)))
        (abs x * abs (assign (sign× (sign y) pos) e))) (*-zeror (abs y))
    ∙ ap₂ assign refl (*-zeror (abs x))
    ∙ sym (ap₂ assign refl (*-zeror (abs (assign (sign× (sign x) (sign y)) (abs x * abs y)))))
  *ℤ-associative (possuc x) (possuc y) (possuc z) = ap possuc (lemma x y z)
  *ℤ-associative (possuc x) (possuc y) (negsuc z) = ap negsuc (lemma x y z)
  *ℤ-associative (possuc x) (negsuc y) (possuc z) = ap negsuc (lemma x y z)
  *ℤ-associative (possuc x) (negsuc y) (negsuc z) = ap possuc (lemma x y z)
  *ℤ-associative (negsuc x) (possuc y) (possuc z) = ap negsuc (lemma x y z)
  *ℤ-associative (negsuc x) (possuc y) (negsuc z) = ap possuc (lemma x y z)
  *ℤ-associative (negsuc x) (negsuc y) (possuc z) = ap possuc (lemma x y z)
  *ℤ-associative (negsuc x) (negsuc y) (negsuc z) = ap negsuc (lemma x y z)

  *ℤ-possucl : ∀ x y → possuc x *ℤ y ≡ y +ℤ (pos x *ℤ y)
  *ℤ-possucl x (pos y) =
    assign-pos (y + x * y) ∙ sym (ap (pos y +ℤ_) (assign-pos (x * y)))
  *ℤ-possucl zero    (negsuc y) = ap negsuc (+-zeror y)
  *ℤ-possucl (suc x) (negsuc y) = ap negsuc p where
    p : y + suc (y + x * suc y) ≡ suc (y + (y + x * suc y))
    p = nat!

  *ℤ-negsucl : ∀ x y → negsuc (suc x) *ℤ y ≡ negℤ y +ℤ (negsuc x *ℤ y)
  *ℤ-negsucl x posz       = sym (+ℤ-zerol (assign neg (x * 0)))
  *ℤ-negsucl x (possuc y) = ap negsuc p where
    p : y + suc x * suc y ≡ suc (y + (y + x * suc y))
    p = nat!
  *ℤ-negsucl x (negsuc y) = ap possuc p where
    p : y + suc x * suc y ≡ y + suc (y + x * suc y)
    p = nat!

  sign×-commutative : ∀ s s' → sign× s s' ≡ sign× s' s
  sign×-commutative pos pos = refl
  sign×-commutative pos neg = refl
  sign×-commutative neg pos = refl
  sign×-commutative neg neg = refl

  *ℤ-commutative : ∀ x y → x *ℤ y ≡ y *ℤ x
  *ℤ-commutative x y = ap₂ assign (sign×-commutative _ _) (*-commutative (abs x) (abs y))

  dot-is-mul : ∀ x y → (dotℤ x y) ≡ (x *ℤ y)
  dot-is-mul posz y = refl
  dot-is-mul (possuc x) y =
      ap (y +ℤ_) (dot-is-mul (pos x) y)
    ∙ sym (*ℤ-possucl x y)
  dot-is-mul (negsuc zero) posz = refl
  dot-is-mul (negsuc zero) (possuc x) = ap negsuc (sym (+-zeror x))
  dot-is-mul (negsuc zero) (negsuc x) = ap possuc (sym (+-zeror x))
  dot-is-mul (negsuc (suc x)) y = sym (*ℤ-negsucl x y ∙ ap (negℤ y +ℤ_) (sym (dot-is-mul (negsuc x) y)))

  private
    distrib-lemma
      : ∀ x y z w → (x +ℤ y) +ℤ (z +ℤ w) ≡ (x +ℤ z) +ℤ (y +ℤ w)
    distrib-lemma x y z w =
        +ℤ-assoc (x +ℤ y) z w
      ·· ap (_+ℤ w) (sym (+ℤ-assoc x y z) ·· ap (x +ℤ_) (+ℤ-commutative y z) ·· +ℤ-assoc x z y)
      ·· sym (+ℤ-assoc (x +ℤ z) y w)

  dot-distribr : ∀ x y z → dotℤ z (x +ℤ y) ≡ (dotℤ z x) +ℤ (dotℤ z y)
  dot-distribr x y posz = refl
  dot-distribr x y (possuc z) =
      ap ((x +ℤ y) +ℤ_) (dot-distribr x y (pos z))
    ∙ distrib-lemma x y (dotℤ (pos z) x) (dotℤ (pos z) y)
  dot-distribr x y (negsuc zero)    = negℤ-distrib x y
  dot-distribr x y (negsuc (suc z)) =
      ap₂ _+ℤ_ (negℤ-distrib x y) (dot-distribr x y (negsuc z))
    ∙ distrib-lemma (negℤ x) (negℤ y) (dotℤ (negsuc z) x) (dotℤ (negsuc z) y)

  *ℤ-distribl : ∀ x y z → x *ℤ (y +ℤ z) ≡ (x *ℤ y) +ℤ (x *ℤ z)
  *ℤ-distribl x y z =
      sym (dot-is-mul x (y +ℤ z))
    ·· dot-distribr y z x
    ·· ap₂ _+ℤ_ (dot-is-mul x y) (dot-is-mul x z)

  *ℤ-distribr : ∀ x y z → (y +ℤ z) *ℤ x ≡ (y *ℤ x) +ℤ (z *ℤ x)
  *ℤ-distribr x y z =
      *ℤ-commutative (y +ℤ z) x
    ·· *ℤ-distribl x y z
    ·· ap₂ _+ℤ_ (*ℤ-commutative x y) (*ℤ-commutative x z)
```
