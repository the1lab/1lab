<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Instances.Integers
open import Algebra.Group.Ab
open import Algebra.Group

open import Data.Int.Divisible
open import Data.Nat.DivMod
open import Data.Dec.Base
open import Data.Fin hiding (_<_)
open import Data.Int hiding (Positive ; _<_ ; <-weaken)
open import Data.Nat as Nat

open import Data.Irr
```
-->

```agda
module Data.Int.DivMod where
```

<!--
```agda
private module ℤ = Abelian-group-on (ℤ-ab .snd)
```
-->

# Integer division {defines="integer-division"}

We define the division $a/b$ where $a$ is an [[integer]] and $b$ is
a positive [[natural number]].

```agda
record DivModℤ (a : Int) (b : Nat) : Type where
  constructor divmodℤ

  field
    quotℤ : Int
    remℤ  : Nat
    quotient : Irr (a ≡ quotℤ *ℤ pos b +ℤ pos remℤ)
    smaller  : remℤ < b

open DivModℤ
```

In order to compute integer division, we reuse [[natural division]].
We proceed by cases: if $a$ is positive, we can simply compute the
division $a/b$ as natural numbers.

```agda
divide-posℤ : ∀ a b → ⦃ _ : Positive b ⦄ → DivModℤ a b
divide-posℤ (pos a) b using divmod q r p s ← divide-pos a b
  = divmodℤ (pos q) r (forget (ap pos (recover p) ∙ sym (ap (_+ℤ pos r) (assign-pos _)))) s
```

If $a$ is negative, we can compute $(-a)/b$ as natural numbers and
distinguish two cases: if the remainder is $0$, then $b$ divides $a$,
so we simply negate the quotient and set the remainder to $0$.

```agda
divide-posℤ (negsuc a) b@(suc b') with divide-pos (suc a) b
... | divmod q zero p s = divmodℤ (assign neg q) 0
  (forget (ap (assign neg) (recover p) ∙ assign-+ (q * b) 0 ∙ ap (_+ℤ 0) (assign-*l q b)))
  (s≤s 0≤x)
```

If the remainder is non-zero, we have to correct for the fact that
integer division as we've defined it rounds towards $-\infty$, while
natural division rounds towards $0$ (hence towards $+\infty$, for
negative numbers), so we take $-((-a)/b) - 1$ as the quotient and
$b - (-a)\%b$ as the remainder.

```agda
... | divmod q (suc r) p s = divmodℤ (negsuc q) (b - suc r)
  (forget (ap (assign neg) (recover p) ∙ lemma))
  (s≤s (monus-≤ b' r))
```

<details>
<summary>One annoying lemma later, we are done.</summary>

```agda
  where
    lemma : assign neg (q * b + suc r) ≡ pos (b' - r) +ℤ negsuc (b' + q * b)
    lemma =
      assign neg (q * b + suc r)                               ≡⟨ ap (assign neg) (+-commutative (q * b) _) ⟩
      negsuc (r + q * b)                                       ≡˘⟨ negℤ-+ℤ-negsuc r (q * b) ⟩
      negℤ (pos r) +ℤ negsuc (q * b)                           ≡⟨ ap (_+ℤ negsuc (q * b)) (ℤ.insertl {negℤ (pos b')} (+ℤ-invl (pos b')) {negℤ (pos r)}) ⟩
      ⌜ negℤ (pos b') ⌝ +ℤ (pos b' -ℤ pos r) +ℤ negsuc (q * b) ≡˘⟨ ap¡ (assign-neg b') ⟩
      assign neg b' +ℤ (pos b' -ℤ pos r) +ℤ negsuc (q * b)     ≡⟨ ap (_+ℤ negsuc (q * b)) (+ℤ-commutative (assign neg b') (pos b' -ℤ pos r)) ⟩
      (pos b' -ℤ pos r) +ℤ assign neg b' +ℤ negsuc (q * b)     ≡˘⟨ +ℤ-assoc (pos b' -ℤ pos r) _ _ ⟩
      (pos b' -ℤ pos r) +ℤ (assign neg b' +ℤ negsuc (q * b))   ≡⟨ ap₂ _+ℤ_ (pos-pos b' r) (ap (_+ℤ negsuc (q * b)) (assign-neg b')) ⟩
      (b' ℕ- r) +ℤ (negℤ (pos b') +ℤ negsuc (q * b))           ≡⟨ ap ((b' ℕ- r) +ℤ_) (negℤ-+ℤ-negsuc b' (q * b)) ⟩
      (b' ℕ- r) +ℤ negsuc (b' + q * b)                         ≡⟨ ap₂ _+ℤ_ (nat-diff-monus b' r (≤-peel (<-weaken s))) refl ⟩
      pos (b' - r) +ℤ negsuc (b' + q * b)                      ∎
```
</details>

```agda
_/ℤ_ : Int → (b : Nat) → ⦃ _ : Positive b ⦄ → Int
a /ℤ b = divide-posℤ a b .quotℤ

_%ℤ_ : Int → (b : Nat) → ⦃ _ : Positive b ⦄ → Nat
a %ℤ b = divide-posℤ a b .remℤ

is-divmodℤ : ∀ x y → ⦃ _ : Positive y ⦄ → x ≡ (x /ℤ y) *ℤ pos y +ℤ pos (x %ℤ y)
is-divmodℤ x (suc y) = recover (divide-posℤ x (suc y) .quotient)

x%ℤy<y : ∀ x y → ⦃ _ : Positive y ⦄ → (x %ℤ y) < y
x%ℤy<y x (suc y) = divide-posℤ x (suc y) .smaller

infixl 9 _/ℤ_ _%ℤ_
```

## Properties

With the way we've set things up above, there is exactly one way to
divide $a$ by $b$: that is, the type `DivModℤ a b`{.Agda} is a
[[proposition]] for all positive `b`{.Agda}.

```agda
DivModℤ-unique : ∀ a b → ⦃ _ : Positive b ⦄ → is-prop (DivModℤ a b)
DivModℤ-unique a b@(suc b') x@(divmodℤ q r p s) y@(divmodℤ q' r' p' s') = go where
```

To see this, we start by showing that the remainders $r$ and $r'$ are
equal. To that end, we show that $b$ divides their difference; since
both $r$ and $r'$ are less than $b$, their difference must also be,
hence it must be zero.

```agda
  b∣r'-r : b ∣ℤ (r' ℕ- r)
  b∣r'-r .fst = q -ℤ q'
  b∣r'-r .snd =
    (q -ℤ q') *ℤ pos b        ≡⟨ *ℤ-distribr-minus (pos b) q q' ⟩
    q *ℤ pos b -ℤ q' *ℤ pos b ≡⟨ ℤ.equal-sum→equal-diff (q *ℤ pos b) (pos r) (q' *ℤ pos b) (pos r') (sym (recover p) ∙ recover p') ⟩
    pos r' -ℤ pos r           ≡⟨ pos-pos r' r ⟩
    r' ℕ- r                   ∎

  same-r : r ≡ r'
  same-r = dec→dne λ r≠r' → Nat.<-≤-asym
    (s≤s (nat-diff-bounded r' r b' (≤-peel s') (≤-peel s)))
    (m∣ℤsn→m≤sn (λ k → r≠r' (sym (nat-diff-positive r' r k))) b∣r'-r)
```

Since the remainders are equal, we have $q * b = a - r = a - r' = q' * b$;
since multiplication by a positive integer is injective, we must also
have $q = q'$.

```agda
  same-q : q ≡ q'
  same-q = *ℤ-injectiver-possuc b' q q' $
    q *ℤ pos b  ≡⟨ -ℤ-swapl _ _ _ (sym (recover p)) ⟩
    a -ℤ pos r  ≡⟨ ap (λ r → a -ℤ pos r) same-r ⟩
    a -ℤ pos r' ≡˘⟨ -ℤ-swapl _ _ _ (sym (recover p')) ⟩
    q' *ℤ pos b ∎
```

The last two fields are propositions, so this shows that the two
`DivModℤ`{.Agda}s are equal.

```agda
  go : x ≡ y
  go i = divmodℤ (same-q i) (same-r i)
    (is-prop→pathp
      (λ i → hlevel {T = Irr (a ≡ same-q i *ℤ pos b +ℤ pos (same-r i))} 1) p p' i)
    (is-prop→pathp
      (λ i → Nat.≤-is-prop {suc (same-r i)} {b}) s s' i)
```

From this, we deduce that $n$ [[divides|divisibility-of-integers]]
the difference of two integers $x - y$ if and only if $x$ and $y$ have
the same remainder modulo $n$...

```agda
divides-diff→same-rem
  : ∀ n x y → ⦃ _ : Positive n ⦄
  → n ∣ℤ (x -ℤ y) → x %ℤ n ≡ y %ℤ n
divides-diff→same-rem n x y n∣x-y
  using k , z ← ∣ℤ→fibre n∣x-y
  using divmodℤ q r p s ← divide-posℤ x n
  = ap remℤ (DivModℤ-unique _ _ (divmodℤ (q -ℤ k) r (forget p') s) (divide-posℤ y n))
  where
    p' : y ≡ (q -ℤ k) *ℤ pos n +ℤ pos r
    p' =
      y                                            ≡˘⟨ negℤ-negℤ y ⟩
      negℤ (negℤ y)                                ≡⟨ ℤ.insertr (ℤ.inversel {x}) {negℤ (negℤ y)} ⟩
      ⌜ negℤ (negℤ y) +ℤ negℤ x ⌝ +ℤ x             ≡⟨ ap! (+ℤ-commutative (negℤ (negℤ y)) _) ⟩
      ⌜ negℤ x -ℤ negℤ y ⌝ +ℤ x                    ≡˘⟨ ap¡ (negℤ-distrib x (negℤ y)) ⟩
      negℤ ⌜ x -ℤ y ⌝ +ℤ x                         ≡˘⟨ ap¡ z ⟩
      negℤ (k *ℤ pos n) +ℤ x                       ≡⟨ ap (negℤ (k *ℤ pos n) +ℤ_) (recover p) ⟩
      negℤ (k *ℤ pos n) +ℤ (q *ℤ pos n +ℤ pos r)   ≡⟨ +ℤ-assoc (negℤ (k *ℤ pos n)) _ _ ⟩
      ⌜ negℤ (k *ℤ pos n) +ℤ q *ℤ pos n ⌝ +ℤ pos r ≡⟨ ap! (+ℤ-commutative (negℤ (k *ℤ pos n)) _) ⟩
      ⌜ q *ℤ pos n -ℤ k *ℤ pos n ⌝ +ℤ pos r        ≡˘⟨ ap¡ (*ℤ-distribr-minus (pos n) q k) ⟩
      (q -ℤ k) *ℤ pos n +ℤ pos r                   ∎

same-rem→divides-diff
  : ∀ n x y → ⦃ _ : Positive n ⦄
  → x %ℤ n ≡ y %ℤ n → n ∣ℤ (x -ℤ y)
same-rem→divides-diff n x y p = dividesℤ (x /ℤ n -ℤ y /ℤ n) $
  (x /ℤ n -ℤ y /ℤ n) *ℤ pos n                                            ≡⟨ *ℤ-distribr-minus (pos n) (x /ℤ n) (y /ℤ n) ⟩
  x /ℤ n *ℤ pos n -ℤ y /ℤ n *ℤ pos n                                     ≡˘⟨ -ℤ-cancelr (pos (x %ℤ n)) (x /ℤ n *ℤ pos n) _ ⟩
  x /ℤ n *ℤ pos n +ℤ pos (x %ℤ n) -ℤ (y /ℤ n *ℤ pos n +ℤ pos ⌜ x %ℤ n ⌝) ≡⟨ ap! p ⟩
  x /ℤ n *ℤ pos n +ℤ pos (x %ℤ n) -ℤ (y /ℤ n *ℤ pos n +ℤ pos (y %ℤ n))   ≡˘⟨ ap₂ _-ℤ_ (is-divmodℤ x n) (is-divmodℤ y n) ⟩
  x -ℤ y                                                                 ∎
```

...and that natural numbers below $n$ are their own remainder modulo $n$.

```agda
Fin-%ℤ : ∀ {n} (i : Fin n) → ⦃ _ : Positive n ⦄ → pos (i .lower) %ℤ n ≡ i .lower
Fin-%ℤ {n} (fin i ⦃ p ⦄) = ap remℤ (DivModℤ-unique (pos i) n
  (divide-posℤ (pos i) n) (divmodℤ 0 i (forget refl) p))
```

We also show that $n$ divides $x$ if and only if $x \% n = 0$.

```agda
rem-zero→divides : ∀ n x → ⦃ _ : Positive n ⦄ → x %ℤ n ≡ 0 → n ∣ℤ x
rem-zero→divides n x p = dividesℤ (x /ℤ n) $
  x /ℤ n *ℤ pos n                 ≡˘⟨ +ℤ-zeror _ ⟩
  x /ℤ n *ℤ pos n +ℤ pos ⌜ 0 ⌝    ≡˘⟨ ap¡ p ⟩
  x /ℤ n *ℤ pos n +ℤ pos (x %ℤ n) ≡˘⟨ is-divmodℤ x n ⟩
  x                               ∎

divides→rem-zero : ∀ n x → ⦃ _ : Positive n ⦄ → n ∣ℤ x → x %ℤ n ≡ 0
divides→rem-zero n@(suc _) x ⦃ p ⦄ n∣x = divides-diff→same-rem n x 0 ⦃ p ⦄
  (subst (fibre (_*ℤ pos n)) (sym (+ℤ-zeror x)) (∣ℤ→fibre n∣x))
```
