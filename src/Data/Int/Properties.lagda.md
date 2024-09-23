<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Nat.Order
open import Data.Int.Base
open import Data.Nat.Base hiding (Positive)
open import Data.Sum.Base
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

  nat-diff-positive : ∀ a b → a ℕ- b ≡ 0 → a ≡ b
  nat-diff-positive a zero p          = pos-injective p
  nat-diff-positive zero (suc b) p    = absurd (negsuc≠pos p)
  nat-diff-positive (suc a) (suc b) p = ap suc (nat-diff-positive a b p)

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

  nat-diff-monus : ∀ x y → y ≤ x → x ℕ- y ≡ pos (x - y)
  nat-diff-monus x y 0≤x                         = refl
  nat-diff-monus (suc x) (suc zero) (s≤s y≤x)    = refl
  nat-diff-monus (suc x) (suc (suc y)) (s≤s y≤x) = nat-diff-monus x (suc y) y≤x

  nat-diff-bounded : ∀ a b c → a ≤ c → b ≤ c → abs (a ℕ- b) ≤ c
  nat-diff-bounded a zero c ac bc          = ac
  nat-diff-bounded zero (suc b) c ac bc    = bc
  nat-diff-bounded (suc a) (suc b) c ac bc = nat-diff-bounded a b c (<-weaken ac) (<-weaken bc)
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

## Absolute value

```agda
  abs-positive : ∀ x → abs x ≡ 0 → x ≡ 0
  abs-positive (pos x) p = ap pos p
  abs-positive (negsuc x) p = absurd (suc≠zero p)

  abs-negℤ : ∀ z → abs (negℤ z) ≡ abs z
  abs-negℤ (posz) = refl
  abs-negℤ (possuc _) = refl
  abs-negℤ (negsuc _) = refl
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

  +ℤ-onel : ∀ x → 1 +ℤ x ≡ sucℤ x
  +ℤ-onel x = +ℤ-sucl 0 x ∙ ap sucℤ (+ℤ-zerol x)

  +ℤ-oner : ∀ x → x +ℤ 1 ≡ sucℤ x
  +ℤ-oner x = +ℤ-sucr x 0 ∙ ap sucℤ (+ℤ-zeror x)

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

  negℤ-+ℤ-negsuc : ∀ a b → negℤ (pos a) +ℤ negsuc b ≡ negsuc (a + b)
  negℤ-+ℤ-negsuc a b =
      +ℤ-commutative (negℤ (pos a)) (negsuc b)
    ·· sym (negℤ-distrib (possuc b) (pos a))
    ·· ap negsuc (+-commutative b a)

  pos-pos : ∀ a b → pos a -ℤ pos b ≡ a ℕ- b
  pos-pos a zero = +ℤ-zeror _
  pos-pos a (suc b) = refl

  -ℤ-swapl : ∀ a b c → a +ℤ b ≡ c → a ≡ c -ℤ b
  -ℤ-swapl a b c p =
      sym (+ℤ-zeror _)
    ∙ ap (a +ℤ_) (sym (+ℤ-invr b))
    ·· +ℤ-assoc a _ _
    ·· ap (_+ℤ negℤ b) p

  private
    distrib-lemma
      : ∀ x y z w → (x +ℤ y) +ℤ (z +ℤ w) ≡ (x +ℤ z) +ℤ (y +ℤ w)
    distrib-lemma x y z w =
        +ℤ-assoc (x +ℤ y) z w
      ·· ap (_+ℤ w) (sym (+ℤ-assoc x y z) ·· ap (x +ℤ_) (+ℤ-commutative y z) ·· +ℤ-assoc x z y)
      ·· sym (+ℤ-assoc (x +ℤ z) y w)

  -ℤ-cancelr : ∀ k x y → (x +ℤ k) -ℤ (y +ℤ k) ≡ x -ℤ y
  -ℤ-cancelr k x y =
    (x +ℤ k) -ℤ (y +ℤ k)      ≡⟨ ap ((x +ℤ k) +ℤ_) (negℤ-distrib y k) ⟩
    (x +ℤ k) +ℤ (negℤ y -ℤ k) ≡⟨ distrib-lemma x k (negℤ y) (negℤ k) ⟩
    (x -ℤ y) +ℤ (k -ℤ k)      ≡⟨ ap ((x -ℤ y) +ℤ_) (+ℤ-invr k) ⟩
    (x -ℤ y) +ℤ 0             ≡⟨ +ℤ-zeror (x -ℤ y) ⟩
    x -ℤ y                    ∎
```

## Multiplication

```agda
  assign-pos : ∀ x → assign pos x ≡ pos x
  assign-pos zero    = refl
  assign-pos (suc x) = refl

  assign-neg : ∀ x → assign neg x ≡ negℤ (pos x)
  assign-neg zero    = refl
  assign-neg (suc x) = refl

  neg-sign : Sign → Sign
  neg-sign pos = neg
  neg-sign neg = pos

  neg-assign : ∀ {s} x → assign (neg-sign s) x ≡ negℤ (assign s x)
  neg-assign {pos} zero = refl
  neg-assign {pos} (suc x) = refl
  neg-assign {neg} zero = refl
  neg-assign {neg} (suc x) = refl

  assign-+ : ∀ {s} x y → assign s (x + y) ≡ assign s x +ℤ assign s y
  assign-+ {pos} zero y = sym (+ℤ-zerol _)
  assign-+ {pos} (suc x) zero = refl
  assign-+ {pos} (suc x) (suc y) = refl
  assign-+ {neg} zero y = sym (+ℤ-zerol _)
  assign-+ {neg} (suc x) zero = ap negsuc (+-zeror _)
  assign-+ {neg} (suc x) (suc y) = ap negsuc (+-sucr _ _)

  possuc≠assign-neg : ∀ {x y} → possuc x ≠ assign neg y
  possuc≠assign-neg {x} {zero} p = suc≠zero (pos-injective p)
  possuc≠assign-neg {x} {suc y} p = pos≠negsuc p

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

  assign-*l : ∀ {s} x y → assign s (x * y) ≡ assign s x *ℤ pos y
  assign-*l {pos} zero y = sym (*ℤ-zerol (pos y))
  assign-*l {pos} (suc x) y = refl
  assign-*l {neg} zero y = refl
  assign-*l {neg} (suc x) y = refl

  *ℤ-negl : ∀ x y → negℤ x *ℤ y ≡ negℤ (x *ℤ y)
  *ℤ-negl posz y = refl
  *ℤ-negl (possuc x) y with sign y
  ... | pos = neg-assign (suc x * abs y)
  ... | neg = neg-assign (suc x * abs y)
  *ℤ-negl (negsuc x) y with sign y
  ... | pos = neg-assign (suc x * abs y)
  ... | neg = neg-assign (suc x * abs y)

  private
    lemma : ∀ x y z → z + y * suc z + x * suc (z + y * suc z)  ≡ z + (y + x * suc y) * suc z
    lemma x y z = nat!

    -- *ℤ-def : ∀ x y → x *ℤ y ≡ assign (sign× (sign x) (sign y)) (abs x * abs y)

  *ℤ-associative : ∀ x y z → x *ℤ (y *ℤ z) ≡ (x *ℤ y) *ℤ z
  *ℤ-associative posz y z = refl
  *ℤ-associative (pos x@(suc _)) posz z = ap (assign pos) (*-zeror x) ∙ sym (ap₂ _*ℤ_ (ap (assign pos) (*-zeror x)) refl)
  *ℤ-associative (negsuc x) posz z = ap (assign neg) (*-zeror x) ∙ sym (ap₂ _*ℤ_ (ap (assign neg) (*-zeror x)) refl)
  *ℤ-associative x (pos y) posz = ap₂ _*ℤ_ (λ i → x) (ap (assign pos) (*-zeror y)) ∙ *ℤ-zeror x ∙ sym (*ℤ-zeror (x *ℤ pos y))
  *ℤ-associative x (negsuc y) posz = ap₂ _*ℤ_ (λ i → x) (ap (assign neg) (*-zeror y)) ∙ *ℤ-zeror x ∙ sym (*ℤ-zeror (x *ℤ negsuc y))
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
  *ℤ-commutative (pos x) (pos y) = ap (assign pos) (*-commutative x y)
  *ℤ-commutative (pos x) (negsuc y) = ap (assign neg) (*-commutative x (suc y))
  *ℤ-commutative (negsuc x) (pos y) = ap (assign neg) (*-commutative (suc x) y)
  *ℤ-commutative (negsuc x) (negsuc y) = ap (assign pos) (*-commutative (suc x) (suc y))

  dot-is-mul : ∀ x y → (dotℤ x y) ≡ (x *ℤ y)
  dot-is-mul posz y = refl
  dot-is-mul (possuc x) y =
      ap (y +ℤ_) (dot-is-mul (pos x) y)
    ∙ sym (*ℤ-possucl x y)
  dot-is-mul (negsuc zero) posz = refl
  dot-is-mul (negsuc zero) (possuc x) = ap negsuc (sym (+-zeror x))
  dot-is-mul (negsuc zero) (negsuc x) = ap possuc (sym (+-zeror x))
  dot-is-mul (negsuc (suc x)) y = sym (*ℤ-negsucl x y ∙ ap (negℤ y +ℤ_) (sym (dot-is-mul (negsuc x) y)))

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

  *ℤ-distribr-minus : ∀ x y z → (y -ℤ z) *ℤ x ≡ (y *ℤ x) -ℤ (z *ℤ x)
  *ℤ-distribr-minus x y z = *ℤ-distribr x y (negℤ z) ∙ ap (y *ℤ x +ℤ_) (*ℤ-negl z x)

  *ℤ-sucr : ∀ x y → x *ℤ sucℤ y ≡ x *ℤ y +ℤ x
  *ℤ-sucr x y =
    x *ℤ sucℤ y      ≡˘⟨ ap (x *ℤ_) (+ℤ-oner y) ⟩
    x *ℤ (y +ℤ 1)    ≡⟨ *ℤ-distribl x y 1 ⟩
    x *ℤ y +ℤ x *ℤ 1 ≡⟨ ap (x *ℤ y +ℤ_) (*ℤ-oner x) ⟩
    x *ℤ y +ℤ x      ∎

  *ℤ-injectiver-possuc : ∀ k x y → x *ℤ possuc k ≡ y *ℤ possuc k → x ≡ y
  *ℤ-injectiver-possuc k (pos x) (pos y) p =
    ap pos (*-suc-inj k x y (pos-injective (sym (assign-pos _) ·· p ·· assign-pos _)))
  *ℤ-injectiver-possuc k (pos x) (negsuc y) p = absurd (pos≠negsuc (sym (assign-pos (x * suc k)) ∙ p))
  *ℤ-injectiver-possuc k (negsuc x) (pos y) p = absurd (negsuc≠pos (p ∙ assign-pos (y * suc k)))
  *ℤ-injectiver-possuc k (negsuc x) (negsuc y) p =
    ap (assign neg) (*-suc-inj k (suc x) (suc y) (ap suc (negsuc-injective p)))

  *ℤ-injectiver-negsuc : ∀ k x y → x *ℤ negsuc k ≡ y *ℤ negsuc k → x ≡ y
  *ℤ-injectiver-negsuc k (pos x) (pos y) p = ap pos (*-suc-inj k x y (pos-injective (negℤ-injective _ _ (sym (assign-neg _) ·· p ·· assign-neg _))))
  *ℤ-injectiver-negsuc k posz (negsuc y) p = absurd (zero≠suc (pos-injective p))
  *ℤ-injectiver-negsuc k (possuc x) (negsuc y) p = absurd (negsuc≠pos p)
  *ℤ-injectiver-negsuc k (negsuc x) posz p = absurd (suc≠zero (pos-injective p))
  *ℤ-injectiver-negsuc k (negsuc x) (possuc y) p = absurd (pos≠negsuc p)
  *ℤ-injectiver-negsuc k (negsuc x) (negsuc y) p = ap (assign neg) (*-suc-inj k (suc x) (suc y) (ap suc (suc-inj (pos-injective p))))

  *ℤ-injectiver : ∀ k x y → k ≠ 0 → x *ℤ k ≡ y *ℤ k → x ≡ y
  *ℤ-injectiver posz x y k≠0 p = absurd (k≠0 refl)
  *ℤ-injectiver (possuc k) x y k≠0 p = *ℤ-injectiver-possuc k x y p
  *ℤ-injectiver (negsuc k) x y k≠0 p = *ℤ-injectiver-negsuc k x y p

  *ℤ-is-zero : ∀ x y → (x *ℤ y) ≡ 0 → (x ≡ 0) ⊎ (y ≡ 0)
  *ℤ-is-zero posz (pos _)    _ = inl refl
  *ℤ-is-zero (negsuc _) posz _ = inr refl
  *ℤ-is-zero posz (negsuc _) _ = inl refl
  *ℤ-is-zero (possuc _) posz _ = inr refl
  *ℤ-is-zero (possuc _) (possuc _) p = absurd (suc≠zero (pos-injective p))
  *ℤ-is-zero (possuc _) (negsuc _) p = absurd (negsuc≠pos p)
  *ℤ-is-zero (negsuc _) (possuc _) p = absurd (negsuc≠pos p)
  *ℤ-is-zero (negsuc _) (negsuc _) p = absurd (suc≠zero (pos-injective p))

  abs-assign : ∀ s n → abs (assign s n) ≡ n
  abs-assign pos zero = refl
  abs-assign pos (suc n) = refl
  abs-assign neg zero = refl
  abs-assign neg (suc n) = refl

  abs-*ℤ : ∀ x y → abs (x *ℤ y) ≡ abs x * abs y
  abs-*ℤ (pos x) (pos y) = abs-assign pos (x * y)
  abs-*ℤ (pos x) (negsuc y) = abs-assign neg (x * suc y)
  abs-*ℤ (negsuc x) (pos y) = abs-assign neg (y + x * y)
  abs-*ℤ (negsuc x) (negsuc y) = refl

  sign-*ℤ-positive : ∀ x t → Positive t → sign (x *ℤ t) ≡ sign x
  sign-*ℤ-positive (pos x) (possuc y) (pos _) = ap sign (assign-pos (x * suc y))
  sign-*ℤ-positive (negsuc x) (possuc y) (pos _) = refl

  assign-sign : ∀ x → assign (sign x) (abs x) ≡ x
  assign-sign posz = refl
  assign-sign (possuc _) = refl
  assign-sign (negsuc _) = refl

  assign-pos-positive : ∀ x → Positive x → assign pos (abs x) ≡ x
  assign-pos-positive x@(possuc _) (pos _) = refl

  divides-*ℤ : ∀ {n k m} → k * n ≡ abs m → pos k *ℤ assign (sign m) n ≡ m
  divides-*ℤ {zero} {k} {pos x} p = ap (assign pos) (*-zeror k) ∙ ap Int.pos (sym (*-zeror k) ∙ p)
  divides-*ℤ {suc n} {k} {posz} p = ap (assign pos) p
  divides-*ℤ {suc n} {zero} {possuc x} p = ap pos p
  divides-*ℤ {suc n} {suc k} {possuc x} p = ap pos p
  divides-*ℤ {zero} {k} {negsuc x} p = absurd (zero≠suc (sym (*-zeror k) ∙ p))
  divides-*ℤ {suc n} {zero} {negsuc x} p = absurd (zero≠suc p)
  divides-*ℤ {suc n} {suc k} {negsuc x} p = ap negsuc (suc-inj p)
```

## Positivity

```agda
*ℤ-positive : ∀ {x y} → Positive x → Positive y → Positive (x *ℤ y)
*ℤ-positive (pos x) (pos y) = pos (y + x * suc y)

*ℤ-nonzero : ∀ {x y} → x ≠ 0 → y ≠ 0 → (x *ℤ y) ≠ 0
*ℤ-nonzero {x} {y} x≠0 y≠0 p with *ℤ-is-zero x y p
... | inl x=0 = x≠0 x=0
... | inr y=0 = y≠0 y=0

+ℤ-positive : ∀ {x y} → Positive x → Positive y → Positive (x +ℤ y)
+ℤ-positive (pos x) (pos y) = pos (x + suc y)

pos-positive : ∀ {x} → x ≠ 0 → Positive (pos x)
pos-positive {zero} 0≠0 = absurd (0≠0 refl)
pos-positive {suc n} _ = pos n

positive→nonzero : ∀ {x} → Positive x → x ≠ 0
positive→nonzero .{possuc x} (pos x) p = suc≠zero (pos-injective p)

*ℤ-positive-cancel : ∀ {x y} → Positive x → Positive (x *ℤ y) → Positive y
*ℤ-positive-cancel {pos .(suc x)} {posz} (pos x) q = absurd (positive→nonzero q (ap (assign pos) (*-zeror x)))
*ℤ-positive-cancel {pos .(suc x)} {possuc y} (pos x) q = pos y

*ℤ-nonzero-cancel : ∀ {x y} → (x *ℤ y) ≠ 0 → x ≠ 0
*ℤ-nonzero-cancel {x} {y} xy≠0 x=0 = absurd (xy≠0 (ap (_*ℤ y) x=0))
```
